#ifndef POLYSAT_LOG_HPP
#define POLYSAT_LOG_HPP


#include <cstdint>
#include <iostream>
#include <string>
#include "math/polysat/log_helper.h"


// By default, enable logging only in debug mode
#ifndef POLYSAT_LOGGING_ENABLED
#   ifndef NDEBUG
#       define POLYSAT_LOGGING_ENABLED 1
#   else
#       define POLYSAT_LOGGING_ENABLED 0
#   endif
#endif


char const* color_blue();
char const* color_yellow();
char const* color_red();
char const* color_reset();


#if POLYSAT_LOGGING_ENABLED

void set_log_enabled(bool log_enabled);
bool get_log_enabled();

class scoped_set_log_enabled {
    bool m_prev;
public:
    scoped_set_log_enabled(bool enabled) {
      m_prev = get_log_enabled();
      set_log_enabled(enabled);
    }
    ~scoped_set_log_enabled() {
      set_log_enabled(m_prev);
    }
};

class polysat_log_indent
{
  int m_amount;
public:
  polysat_log_indent(int amount);
  ~polysat_log_indent();
};

/// Lower log level means more important
enum class LogLevel : int {
  None = 0,
  Heading1 = 1,
  Heading2 = 2,
  Heading3 = 3,
  Default = 4,
  Verbose = 5,
};

/// Filter log messages
bool
polysat_should_log(LogLevel msg_level, std::string fn, std::string pretty_fn);

std::pair<std::ostream&, bool>
polysat_log(LogLevel msg_level, std::string fn, std::string pretty_fn);

#ifdef _MSC_VER
#define __PRETTY_FUNCTION__ __FUNCSIG__
#endif

#define LOG_(lvl, x)                                               \
  do {                                                             \
    if (polysat_should_log(lvl, __func__, __PRETTY_FUNCTION__)) {  \
      auto pair = polysat_log(lvl, __func__, __PRETTY_FUNCTION__); \
      std::ostream& os = pair.first;                               \
      bool should_reset = pair.second;                             \
      os << x;                                                     \
      if (should_reset)                                            \
        os << color_reset();                                       \
      os << std::endl;                                             \
    }                                                              \
  } while (false)

#define LOG_CONCAT_HELPER(a,b) a ## b
#define LOG_CONCAT(a,b) LOG_CONCAT_HELPER(a,b)

#define LOG_INDENT(lvl, x)  \
  LOG_(lvl, x);             \
  polysat_log_indent LOG_CONCAT(polysat_log_indent_obj_, __LINE__) (4);

#define LOG_H1(x) LOG_INDENT(LogLevel::Heading1, x)
#define LOG_H2(x) LOG_INDENT(LogLevel::Heading2, x)
#define LOG_H3(x) LOG_INDENT(LogLevel::Heading3, x)
#define LOG(x)    LOG_(LogLevel::Default , x)
#define LOG_V(x)  LOG_(LogLevel::Verbose , x)
#define COND_LOG(c, x) if (c) LOG(x)
#define LOGE(x)   LOG(#x << " = " << (x))

#define IF_LOGGING(x) \
  do {                \
    x;                \
  } while (false)


#else  // POLYSAT_LOGGING_ENABLED

inline void set_log_enabled(bool) {}
inline bool get_log_enabled() { return false; }
class scoped_set_log_enabled {};

#define LOG_(lvl, x)  \
  do {               \
    /* do nothing */ \
  } while (false)

#define LOG_H1(x) LOG_(0, x)
#define LOG_H2(x) LOG_(0, x)
#define LOG_H3(x) LOG_(0, x)
#define LOG(x)    LOG_(0, x)
#define LOG_V(x)  LOG_(0, x)
#define COND_LOG(c, x)  LOG_(c, x)
#define LOGE(x)   LOG_(0, x)

#define IF_LOGGING(x) \
  do {                \
    /* do nothing */  \
  } while (false)

#endif  // POLYSAT_LOGGING_ENABLED


#endif  // POLYSAT_LOG_HPP
