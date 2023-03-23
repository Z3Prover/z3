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
};

/// Filter log messages
bool
polysat_should_log(unsigned verbose_lvl, LogLevel msg_level, std::string fn, std::string pretty_fn);

std::pair<std::ostream&, bool>
polysat_log(LogLevel msg_level, std::string fn, std::string pretty_fn);

#ifdef _MSC_VER
#define __PRETTY_FUNCTION__ __FUNCSIG__
#endif

#define LOG_(verbose_lvl, log_lvl, x)                                               \
  do {                                                                              \
    if (polysat_should_log(verbose_lvl, log_lvl, __func__, __PRETTY_FUNCTION__)) {  \
      auto pair = polysat_log(log_lvl, __func__, __PRETTY_FUNCTION__);              \
      std::ostream& os = pair.first;                                                \
      bool should_reset = pair.second;                                              \
      os << x;                                                                      \
      if (should_reset)                                                             \
        os << color_reset();                                                        \
      os << std::endl;                                                              \
    }                                                                               \
  } while (false)

#define LOG_CONCAT_HELPER(a,b) a ## b
#define LOG_CONCAT(a,b) LOG_CONCAT_HELPER(a,b)

#define LOG_INDENT(verbose_lvl, log_lvl, x)  \
  LOG_(verbose_lvl, log_lvl, x);             \
  polysat_log_indent LOG_CONCAT(polysat_log_indent_obj_, __LINE__) (4);

#define LOG_H1(x) LOG_INDENT(0, LogLevel::Heading1, x)
#define LOG_H2(x) LOG_INDENT(0, LogLevel::Heading2, x)
#define LOG_H3(x) LOG_INDENT(0, LogLevel::Heading3, x)
#define LOG(x)    LOG_(0, LogLevel::Default , x)

#define LOG_H1_V(verbose_lvl, x) LOG_INDENT(verbose_lvl, LogLevel::Heading1, x)
#define LOG_H2_V(verbose_lvl, x) LOG_INDENT(verbose_lvl, LogLevel::Heading2, x)
#define LOG_H3_V(verbose_lvl, x) LOG_INDENT(verbose_lvl, LogLevel::Heading3, x)
#define LOG_V(verbose_lvl, x)    LOG_(verbose_lvl, LogLevel::Default , x)

#define COND_LOG(c, x) if (c) LOG(x)
#define LOGE(x)   LOG(#x << " = " << (x))

#define IF_LOGGING(x)           \
  do {                          \
      if (get_log_enabled()) {  \
        x;                      \
      }                         \
  } while (false)


#else  // POLYSAT_LOGGING_ENABLED

inline void set_log_enabled(bool) {}
inline bool get_log_enabled() { return false; }
class scoped_set_log_enabled {};

#define LOG_(vlvl, lvl, x)  \
  do {                      \
    /* do nothing */        \
  } while (false)

#define LOG_H1(x) LOG_(0, 0, x)
#define LOG_H2(x) LOG_(0, 0, x)
#define LOG_H3(x) LOG_(0, 0, x)
#define LOG(x)    LOG_(0, 0, x)

#define LOG_H1_V(v, x) LOG_(v, 0, x)
#define LOG_H2_V(v, x) LOG_(v, 0, x)
#define LOG_H3_V(v, x) LOG_(v, 0, x)
#define LOG_V(v, x)    LOG_(v, 0, x)

#define COND_LOG(c, x) LOG_(0, c, x)
#define LOGE(x)        LOG_(0, 0, x)

#define IF_LOGGING(x) \
  do {                \
    /* do nothing */  \
  } while (false)

#endif  // POLYSAT_LOGGING_ENABLED


#endif  // POLYSAT_LOG_HPP
