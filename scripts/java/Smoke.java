// Copyright (c) 2026 Microsoft Corporation
import com.microsoft.z3.Context;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Version;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

public final class Smoke {
    private static void solve() {
        try (Context context = new Context()) {
            IntExpr x = context.mkIntConst("x");
            Solver solver = context.mkSolver();
            solver.add(context.mkEq(x, context.mkInt(42)));
            if (solver.check() != Status.SATISFIABLE) {
                throw new AssertionError("Expected SAT");
            }
            solver.add(context.mkEq(x, context.mkInt(43)));
            if (solver.check() != Status.UNSATISFIABLE) {
                throw new AssertionError("Expected UNSAT");
            }
        }
    }

    public static void main(String[] args) throws Exception {
        String mode = args[0];
        if (mode.equals("skip")) {
            System.setProperty("z3.skipLibraryLoad", "true");
            Class.forName("com.microsoft.z3.Native");
        } else if (mode.equals("missing") || mode.equals("unsupported") || mode.equals("temp-failure")) {
            if (mode.equals("unsupported")) {
                System.setProperty("os.arch", "unknown-test-cpu");
            }
            try {
                Class.forName("com.microsoft.z3.Native");
                throw new AssertionError("Expected native loading failure");
            } catch (UnsatisfiedLinkError error) {
                if (error.getCause() == null || error.getSuppressed().length != 2
                        || !error.getMessage().contains("System attempts:")) {
                    throw new AssertionError("Lost loading diagnostics", error);
                }
                String expected = mode.equals("unsupported") ? "unsupported-arch"
                    : mode.equals("missing") ? "Missing bundled native resource" : "Bundled attempt:";
                if (!error.getMessage().contains(expected)) {
                    throw new AssertionError("Wrong failure stage", error);
                }
                if (mode.equals("temp-failure") && !(error.getCause() instanceof java.io.IOException)) {
                    throw new AssertionError("Expected temporary-directory I/O failure", error);
                }
                System.out.println(error.getMessage());
            }
        } else {
            // Start all threads before the first Native initialization.
            ExecutorService executor = Executors.newFixedThreadPool(4);
            try {
                List<Callable<Void>> jobs = new ArrayList<Callable<Void>>();
                for (int i = 0; i < 4; i++) {
                    jobs.add(new Callable<Void>() {
                        public Void call() { solve(); return null; }
                    });
                }
                for (Future<Void> result : executor.invokeAll(jobs)) {
                    result.get();
                }
            } finally {
                executor.shutdownNow();
            }
            String version = Version.getString();
            if (!version.equals(args[1])) {
                throw new AssertionError("Version mismatch: " + version + " != " + args[1]);
            }
            System.out.println("Context/version/SAT/UNSAT/concurrent initialization: " + version);
            if (mode.equals("bundled")) {
                java.io.File[] directories = new java.io.File(System.getProperty("java.io.tmpdir")).listFiles();
                boolean extracted = false;
                if (directories != null) {
                    for (java.io.File directory : directories) {
                        if (directory.getName().startsWith("z3-native-") && directory.isDirectory()
                                && directory.list().length == 2) {
                            extracted = true;
                        }
                    }
                }
                if (!extracted) {
                    throw new AssertionError("Embedded fallback did not extract both libraries");
                }
            }
        }
        System.out.println("PASS " + mode);
    }
}
