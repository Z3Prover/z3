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
// #include <vector>
// #include <typeinfo>

/*
namespace numerical_chars {
inline std::ostream &operator<<(std::ostream &os, char c) {
    return std::is_signed<char>::value ? os << static_cast<int>(c)
                                       : os << static_cast<unsigned int>(c);
}

inline std::ostream &operator<<(std::ostream &os, signed char c) {
    return os << static_cast<int>(c);
}

inline std::ostream &operator<<(std::ostream &os, unsigned char c) {
    return os << static_cast<unsigned int>(c);
}
}
*/


/// Lower log level means more important
enum class LogLevel : int {
  Error = 0,
  Warn = 1,
  Info = 2,
  Debug = 3,
  Trace = 4,
};

/// Filter log messages
bool
polysat_should_log(LogLevel msg_level, std::string fn, std::string pretty_fn);

std::pair<std::ostream&, bool>
polysat_log(LogLevel msg_level, std::string fn, std::string pretty_fn);

#define LOG(lvl, x)                                                \
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

#define LOG_ERROR(x) LOG(LogLevel::Error, x)
#define LOG_WARN(x)  LOG(LogLevel::Warn, x)
#define LOG_INFO(x)  LOG(LogLevel::Info, x)
#define LOG_DEBUG(x) LOG(LogLevel::Debug, x)
#define LOG_TRACE(x) LOG(LogLevel::Trace, x)


#else  // POLYSAT_LOGGING_ENABLED


#define LOG(lvl, x)  \
  do {               \
    /* do nothing */ \
  } while (false)

#define LOG_ERROR(x) LOG(0, x)
#define LOG_WARN(x)  LOG(0, x)
#define LOG_INFO(x)  LOG(0, x)
#define LOG_DEBUG(x) LOG(0, x)
#define LOG_TRACE(x) LOG(0, x)


#endif  // POLYSAT_LOGGING_ENABLED


#endif  // POLYSAT_LOG_HPP
