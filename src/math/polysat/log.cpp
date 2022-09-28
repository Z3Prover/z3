#ifndef _MSC_VER
#include <unistd.h>  // for isatty
#else
#include <windows.h>
#include <io.h>
#undef min
#endif
#include <utility>

#include "util/util.h"
#include "math/polysat/log.h"

/**
For windows:
https://docs.microsoft.com/en-us/cpp/c-runtime-library/reference/isatty?view=msvc-160

So include <io.h> and create platform wrapper for _isatty / isatty.

Other:
- add option to configure z3 trace feature to point to std::err
- roll this functionality into trace.cpp/trace.h in util
- Generally, generic functionality should not reside in specific directories.
- code diverges on coding conventions.
*/

#if POLYSAT_LOGGING_ENABLED

static LogLevel get_max_log_level(std::string const& fn, std::string const& pretty_fn) {
  (void)fn;
  (void)pretty_fn;

  if (fn == "push_cjust")
    return LogLevel::Verbose;

  // if (fn == "pop_levels")
  //   return LogLevel::Default;

  // also covers 'reset_marks' and 'set_marks'
  if (fn.find("set_mark") != std::string::npos)
    return LogLevel::Default;

  // return LogLevel::Verbose;
  return LogLevel::Default;
}

/// Filter log messages
bool polysat_should_log(LogLevel msg_level, std::string fn, std::string pretty_fn) {
  LogLevel max_log_level = get_max_log_level(fn, pretty_fn);
  return msg_level <= max_log_level;
}

static char const* level_color(LogLevel msg_level) {
  switch (msg_level) {
    case LogLevel::Heading1:
      return "[31m"; // red
    case LogLevel::Heading2:
      return "[33m"; // yellow
    case LogLevel::Heading3:
      return "[34m"; // blue
    default:
      return nullptr;
  }
}

int polysat_log_indent_level = 0;

std::pair<std::ostream&, bool> polysat_log(LogLevel msg_level, std::string fn, std::string /* pretty_fn */) {
  std::ostream& os = std::cerr;

  size_t width = 20;
  size_t padding = 0;
  if (width >= fn.size()) 
      padding = width - fn.size();
  else
    fn = fn.substr(0, width - 3) + "...";
  char const* color = nullptr;
  color = level_color(msg_level);
#ifdef _MSC_VER    
  HANDLE hOut = GetStdHandle(STD_ERROR_HANDLE);
  bool ok = hOut != INVALID_HANDLE_VALUE;
  DWORD dwMode = 0;
  ok = ok && GetConsoleMode(hOut, &dwMode);
  dwMode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
  ok = ok && SetConsoleMode(hOut, dwMode);
#else
  int const fd = fileno(stderr);
  if (color && !isatty(fd)) { color = nullptr; }
#endif

  if (color)
    os << color;
  os << "[" << fn << "] " << std::string(padding, ' ');
  os << std::string(polysat_log_indent_level, ' ');
  return {os, (bool)color};

}

polysat_log_indent::polysat_log_indent(int amount): m_amount{amount} {
  polysat_log_indent_level += m_amount;
}

polysat_log_indent::~polysat_log_indent() {
  polysat_log_indent_level -= m_amount;
}


#endif  // POLYSAT_LOGGING_ENABLED
