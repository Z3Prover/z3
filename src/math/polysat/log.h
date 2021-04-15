#ifndef POLYSAT_LOG_HPP
#define POLYSAT_LOG_HPP


// By default, enable logging only in debug mode
#ifndef POLYSAT_LOGGING_ENABLED
#   ifndef NDEBUG
#       define POLYSAT_LOGGING_ENABLED 1
#   else
#       define POLYSAT_LOGGING_ENABLED 0
#   endif
#endif


#if POLYSAT_LOGGING_ENABLED


#include <cstdint>
#include <iostream>
#include <string>


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

#define LOG_(lvl, x)                                               \
  do {                                                             \
    if (polysat_should_log(lvl, __func__, __PRETTY_FUNCTION__)) {  \
      auto pair = polysat_log(lvl, __func__, __PRETTY_FUNCTION__); \
      std::ostream& os = pair.first;                               \
      bool should_reset = pair.second;                             \
      os << x;                                                     \
      if (should_reset) {                                          \
        os << "\x1B[0m"; /* reset color */                         \
      }                                                            \
      os << std::endl;                                             \
    }                                                              \
  } while (false)

#define LOG_H1(x) LOG_(LogLevel::Heading1, x)
#define LOG_H2(x) LOG_(LogLevel::Heading2, x)
#define LOG_H3(x) LOG_(LogLevel::Heading3, x)
#define LOG(x)    LOG_(LogLevel::Default , x)
#define LOG_V(x)  LOG_(LogLevel::Verbose , x)


#else  // POLYSAT_LOGGING_ENABLED


#define LOG_(lvl, x)  \
  do {               \
    /* do nothing */ \
  } while (false)

#define LOG_H1(x) LOG_(0, x)
#define LOG_H2(x) LOG_(0, x)
#define LOG_H3(x) LOG_(0, x)
#define LOG(x)    LOG_(0, x)
#define LOG_V(x)  LOG_(0, x)


#endif  // POLYSAT_LOGGING_ENABLED


#endif  // POLYSAT_LOG_HPP
