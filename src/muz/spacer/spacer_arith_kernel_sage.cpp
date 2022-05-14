/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

   spacer_arith_kernel_sage.cpp

Abstract:

   Matrix kernel computation using Sage

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

  USED FOR DEBUGGING AND PROTOTYPING ONLY!!!
--*/

#include "muz/spacer/spacer_arith_kernel.h"
#include "util/stopwatch.h"
#include "util/util.h"

#include <csignal>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <istream>
#include <sstream>
#include <sys/wait.h>
#include <unistd.h>

using namespace spacer;

namespace {
/**
Abstracts interface to Sage.

Supports initialization and writing to Sage.

To get output from Sage, write to file and read from the file.

HG: Could not find standard methods to convert file descriptors to streams.
*/
class Sage {
    FILE *m_out;
    FILE *m_in;
    std::string tmp_name;
    pid_t child_pid;

    /// Test sage communication
    bool test();

  public:
    /// Start sage interface
    Sage();
    ~Sage() {
        kill(child_pid, SIGKILL);
        int status;
        waitpid(child_pid, &status, 0);
    }
    FILE *get_ostream() const { return m_out; }
    FILE *get_istream() const { return m_in; }
};

Sage::Sage() {
    int to_sage_pipe[2];
    int from_sage_pipe[2];
    int ok = pipe(to_sage_pipe);
    if (ok) {
        perror("sage pipe1");
        exit(1);
    }
    ok = pipe(from_sage_pipe);
    if (ok) {
        perror("sage pipe2");
        exit(1);
    }

    pid_t pid = fork();
    if (pid) {
        m_out = fdopen(to_sage_pipe[1], "w");
        m_in = fdopen(from_sage_pipe[0], "r");

        /* parent */
        close(to_sage_pipe[0]);
        close(from_sage_pipe[1]);

        child_pid = pid;
        if (!test()) {
            TRACE("sage-interface", tout << "Sage test failed \n";);
        }
    } else if (pid == 0) {
        /* child */

        // setup file descriptor
        close(to_sage_pipe[1]);
        close(from_sage_pipe[0]);
        dup2(to_sage_pipe[0], STDIN_FILENO);
        dup2(from_sage_pipe[1], STDOUT_FILENO);

        // setup arguments, assume sage is in PATH
        char *const argv[3] = {(char *)"sage", NULL, NULL};
        // XXX: sage complains that it can't find $HOME, but works regardless
        execvp("sage", argv);
        perror("execvpe for sage");
    } else {
        perror("fork");
        exit(1);
    }
}

bool Sage::test() {
    char temp_name[] = "/tmp/spacersage.XXXXXX";
    int tmp_fd = mkstemp(temp_name);
    if (tmp_fd == -1) {
        // Error: failed to create temp file
        TRACE("sage-interface", tout << "failed to create temp file\n";);
        return false;
    }
    TRACE("sage-interface",
          tout << "writing test output to " << temp_name << "\n";);
    fprintf(m_out, "f = open (\"\%s\", 'w')\n", temp_name);
    // Do stuff
    fprintf(m_out, "print >>f, 2 + 2\n");
    fprintf(m_out, "f.close()\n");
    fflush(m_out);
    // indicate that sage is done by printing to pipe
    fprintf(m_out, "print \"\\nok\\n\"\n");
    fprintf(m_out, "sys.stdout.flush()\n");
    fflush(m_out);

    // first wait for sage to write ok
    char *std_ok = nullptr;
    size_t n = 0;
    ssize_t t = 0;
    // read all the lines printed by sage until we get okay
    // will block if Sage not found :(
    do {
        t = getline(&std_ok, &n, m_in);
        if (t == -1 || feof(m_in) || ferror(m_in)) {
            TRACE("sage-interface",
                  tout << "error while reading from sage pipe \n";);
            return false;
        }
        CTRACE("sage-interface-verb", t > 0,
               tout << "got sage std output " << std_ok << "\n";);
    } while (strcmp(std_ok, "ok\n") != 0);
    // delete object allocated by getline
    delete std_ok;
    TRACE("sage-interface", tout << "got ok from sage \n";);

    // read output from file
    std::ifstream ifs(temp_name);
    int ok = -1;
    if (!ifs.is_open()) {
        TRACE("sage-interface", tout << "failed to open file\n";);
        return false;
    }

    ifs >> ok;

    if (ifs.bad()) {
        TRACE("sage-interface", tout << "error when reading from file\n";);
        ifs.close();
        close(tmp_fd);
        std::remove(temp_name);
        return false;
    }

    TRACE("sage-interface", tout << "got sage output " << ok << "\n";);
    ifs.close();
    close(tmp_fd);
    // TODO: remove file even if sage/spacer terminates before reaching here
    std::remove(temp_name);
    return ok == 4;
}

class sage_arith_kernel_plugin : public spacer_arith_kernel::plugin {
    struct stats {
        stopwatch watch;
        unsigned m_sage_calls;
        stats() { reset(); }
        void reset() {
            watch.reset();
            m_sage_calls = 0;
        }
    };
    stats m_st;

    scoped_ptr<Sage> m_sage;
    bool compute_kernel(const spacer_matrix &in_matrix,
                        spacer_matrix &out_kernel,
                        vector<unsigned> &basics) override;
    std::string matrix_to_string(const spacer_matrix &matrix) const;

  public:
    sage_arith_kernel_plugin() : m_sage(alloc(Sage)) {}
    ~sage_arith_kernel_plugin() {}

    virtual void collect_statistics(statistics &st) const override {
        st.update("time.spacer.sage", m_st.watch.get_seconds());
        st.update("SPACER sage calls", m_st.m_sage_calls);
    }
    virtual void reset_statistics() override { m_st.reset(); }
    virtual void reset() override { m_sage = alloc(Sage); }
};

std::string
sage_arith_kernel_plugin::matrix_to_string(const spacer_matrix &matrix) const {
    std::stringstream ss;
    ss << "[\n";
    for (unsigned i = 0; i < matrix.num_rows(); i++) {
        ss << "(";
        for (unsigned j = 0; j < matrix.num_cols() - 1; j++) {
            ss << matrix.get(i, j).to_string();
            ss << ", ";
        }
        ss << matrix.get(i, matrix.num_cols() - 1).to_string();
        ss << "),\n";
    }
    ss << "]\n";
    return ss.str();
}

bool sage_arith_kernel_plugin::compute_kernel(const spacer_matrix &in_matrix,
                                              spacer_matrix &out_kernel,
                                              vector<unsigned> &basics) {
    scoped_watch _w_(m_st.watch);

    char temp_name[] = "/tmp/spacersage.XXXXXX";
    int tmp_fd = mkstemp(temp_name);
    if (tmp_fd == -1) {
        // Error: failed to create temp file
        perror("temp file create");
        exit(1);
    }
    m_st.m_sage_calls++;
    TRACE("sage-interface", tout << temp_name << "\n";);
    unsigned n_cols = in_matrix.num_cols();
    unsigned n_rows = in_matrix.num_rows();
    TRACE("sage-interface", tout << "Going to compute kernel of " << n_rows
                                 << " by " << n_cols << " matrix \n"
                                 << matrix_to_string(in_matrix) << "\n";);

    auto out = m_sage->get_ostream();
    fprintf(out, "f = open (\"\%s\", 'w')\n", temp_name);

    // construct  matrix in sage
    std::stringstream ss_stream;
    ss_stream << " a = matrix(ZZ,";
    ss_stream << n_rows;
    ss_stream << (", ");
    ss_stream << (n_cols + 1);
    ss_stream << (", [");
    for (unsigned i = 0; i < n_rows; i++) {
        ss_stream << ("[");
        for (unsigned j = 0; j < n_cols; j++) {
            ss_stream << in_matrix.get(i, j).to_string();
            ss_stream << (", ");
        }
        ss_stream << ("1");
        ss_stream << ("], ");
    }
    ss_stream << ("]);\n");
    fprintf(out, "%s", ss_stream.str().c_str());
    fprintf(out, "c = a.right_kernel().basis();\n");
    fflush(out);
    fprintf(out, "print >> f, len(c);\n");
    fprintf(out, "print >> f, c;\n");
    fprintf(out, "f.close()\n");
    fflush(out);
    fprintf(out, "print \"\\nok\\n\"\n");
    fprintf(out, "sys.stdout.flush()\n");
    fflush(out);

    // first wait for sage to write ok
    char *std_ok = nullptr;
    size_t n = 0;
    ssize_t t = 0;
    // read all the lines printed by sage until we get okay
    auto in = m_sage->get_istream();
    do {
        t = getline(&std_ok, &n, in);
        if (t == -1 || feof(in) || ferror(in)) {
            TRACE("sage-interface",
                  tout << "error while reading from sage pipe \n";);
            return false;
        }
        CTRACE("sage-interface-verb", t > 0,
               tout << "got sage std output " << std_ok << "\n";);
    } while (strcmp(std_ok, "ok\n") != 0);
    // delete object allocated by getline
    delete std_ok;
    TRACE("sage-interface", tout << "got ok from sage \n";);

    // read output from file
    std::ifstream ifs(temp_name);
    if (!ifs.is_open()) {
        TRACE("sage-interface", tout << "failed to open file\n";);
        return false;
    }

    int num;
    unsigned total_rows = 0, row = 0, col = 0;
    char misc_char;
    ifs >> std::skipws;
    ifs >> total_rows;
    if (total_rows == 0) {
        ifs.close();
        close(tmp_fd);
        std::remove(temp_name);
        TRACE("sage-interface", tout << "Rank of kernel is zero\n";);
        return false;
    }
    out_kernel = spacer_matrix(total_rows, n_cols + 1);
    ifs >> misc_char;
    SASSERT(misc_char == '[');
    while (true) {
        while (misc_char != '(' && misc_char != ']') ifs >> misc_char;
        if (misc_char == ']') break;
        SASSERT(misc_char == '(');
        col = 0;
        while (!ifs.bad() && !ifs.eof()) {
            ifs >> num;
            if (ifs.fail() || ifs.bad()) {
                TRACE("sage-interface",
                      tout << "Woops!!! Couldn't read sage output propertly. "
                              "Abording\n";);
                ifs.close();
                close(tmp_fd);
                std::remove(temp_name);
                out_kernel.reset(0);
                SASSERT(false);
                return false;
            }
            ifs >> misc_char;
            out_kernel.set(row, col, rational(num));
            col++;
            if (misc_char == ')') { break; }
            SASSERT(misc_char == ',');
        }
        row++;
    }
    SASSERT(row == total_rows);
    if (ifs.bad()) {
        TRACE("sage-interface", tout << "error when reading from file\n";);
        ifs.close();
        close(tmp_fd);
        std::remove(temp_name);
        return false;
    }

    TRACE("sage-interface", tout << "finished reading sage output\n";);
    ifs.close();

    TRACE("sage-interface",
          tout << "Kernel is " << matrix_to_string(out_kernel) << "\n";);

    close(tmp_fd);
    // TODO: remove file even if sage/spacer terminates before reaching here
    std::remove(temp_name);
    return true;
}

} // namespace

namespace spacer {
spacer_arith_kernel::plugin *mk_sage_plugin() { return nullptr; }
} // namespace spacer
