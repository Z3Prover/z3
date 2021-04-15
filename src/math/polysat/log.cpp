#ifndef _MSC_VER
#include <unistd.h>  // for isatty
#endif
#include <utility>

#include "math/polysat/log.h"

#if POLYSAT_LOGGING_ENABLED

static LogLevel
get_max_log_level(std::string const& fn, std::string const& pretty_fn)
{
  (void)fn;
  (void)pretty_fn;

  // bool const from_decision_queue = pretty_fn.find("DecisionQueue") != std::string::npos;
  // if (from_decision_queue) {
  //   return LogLevel::Info;
  // }

  // if (pretty_fn.find("add_") != std::string::npos) {
  //   return LogLevel::Info;
  // }

  // if (fn == "analyze") {
  //   return LogLevel::Trace;
  // }
  // if (fn.find("minimize") != std::string::npos) {
  //   return LogLevel::Trace;
  // }
  // if (fn == "propagate_literal") {
  //     return LogLevel::Trace;
  // }

  return LogLevel::Verbose;
  // return LogLevel::Warn;
}

/// Filter log messages
bool
polysat_should_log(LogLevel msg_level, std::string fn, std::string pretty_fn)
{
  LogLevel max_log_level = get_max_log_level(fn, pretty_fn);
  return msg_level <= max_log_level;
}

static char const*
level_color(LogLevel msg_level)
{
  switch (msg_level) {
    case LogLevel::Heading1:
      return "\x1B[31m"; // red
    case LogLevel::Heading2:
      return "\x1B[33m"; // yellow
    case LogLevel::Heading3:
      return "\x1B[34m"; // blue
    default:
      return nullptr;
  }
}

int polysat_log_indent_level = 0;

std::pair<std::ostream&, bool>
polysat_log(LogLevel msg_level, std::string fn, std::string /* pretty_fn */)
{
  std::ostream& os = std::cerr;
  int const fd = fileno(stderr);

  size_t width = 20;
  size_t padding = width - std::min(width, fn.size());

#ifdef _MSC_VER
  char const* color = nullptr;
#else
  char const* color = level_color(msg_level);
  if (color && !isatty(fd)) { color = nullptr; }
#endif

  if (color) { os << color; }
  os << "[" << fn << "] " << std::string(padding, ' ');
  os << std::string(polysat_log_indent_level, ' ');
  return {os, (bool)color};
}

polysat_log_indent::polysat_log_indent(int amount)
  : m_amount{amount}
{
  polysat_log_indent_level += m_amount;
}

polysat_log_indent::~polysat_log_indent()
{
  polysat_log_indent_level -= m_amount;
}


#endif  // POLYSAT_LOGGING_ENABLED
