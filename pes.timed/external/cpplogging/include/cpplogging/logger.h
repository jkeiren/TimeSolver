// Author(s): Jeroen Keiren
// Copyright: see the accompanying file COPYING or copy at
// https://svn.win.tue.nl/trac/MCRL2/browser/trunk/COPYING
//
// Distributed under the Boost Software License, Version 1.0.
// (See accompanying file LICENSE_1_0.txt or copy at
// http://www.boost.org/LICENSE_1_0.txt)
//
/// \file logger.h
///
/// This file was originally created as part of the mCRL2
/// toolset, from which I have extracted it for use in future
/// projects.

#ifndef LOGGING_LOGGER_H
#define LOGGING_LOGGER_H

#include <cstdio>
#include <ctime>
#include <stdexcept>
#include <string>
#include <sstream>
#include <memory>
#include <map>
#include <set>

namespace cpplogging {

/// \brief Log levels that are supported
enum log_level_t
{
  quiet, // No log message should ever be printed to this log level!
  error,
  warning,
  info,
  status,
  verbose,
  debug,
  debug1,
  debug2,
  debug3,
  debug4,
  debug5
};

/// \brief Convert log level to string
/// This string is used to prefix messages in the logging output.
inline
std::string log_level_to_string(const log_level_t level)
{
  static const char* const buffer[] = {"quiet", "error", "warning", "info", "status", "verbose", "debug", "debug1", "debug2", "debug3", "debug4", "debug5"};
  return buffer[level];
}

/// \brief Convert string to log level
inline
log_level_t log_level_from_string(const std::string& s)
{
  if (s == "quiet")
  {
    return quiet;
  }
  else if (s == "error")
  {
    return error;
  }
  else if (s == "warning")
  {
    return warning;
  }
  else if (s == "info")
  {
    return info;
  }
  else if (s == "status")
  {
    return status;
  }
  else if (s == "verbose")
  {
    return verbose;
  }
  else if (s == "debug")
  {
    return debug;
  }
  else if (s == "debug1")
  {
    return debug1;
  }
  else if (s == "debug2")
  {
    return debug2;
  }
  else if (s == "debug3")
  {
    return debug3;
  }
  else if (s == "debug4")
  {
    return debug4;
  }
  else if (s == "debug5")
  {
    return debug5;
  }
  else
  {
    throw std::runtime_error("Unknown log-level " + s + " provided.");
  }
}


/// \prototype
//std::string now_time();
std::string format_time(const time_t* timestamp);

/// \brief Interface class for output policy.
///
/// Separates the exact way of doing output from the logger class.
class output_policy
{
  public:
    /// \brief Constructor.
    output_policy()
    {}

    /// \brief Destructor.
    virtual ~output_policy()
    {}

    /// \brief Output message.
    /// \param[in] msg Message that is written to output.
    /// \param[in] hint Hint for the stream to which the output is written.
    ///  \details Any implementation must assure that output is written using an atomic action, to prevent
    /// mixing of different lines into one line in the output.
    virtual void output(const log_level_t level, const std::string& hint, const time_t timestamp, const std::string& msg) = 0;
};

/// \prototype
std::set<output_policy*> initialise_output_policies();

/// \brief Class for logging messages
///
/// Based on a description in the article "Logging In C++", Petru Marginean
/// Dr. Dobb's Journal, September 5, 2007
/// (url: http://drdobbs.com/cpp/201804215)
/// Requires that OutputPolicy is a class which as a static member output(const std::string&)
class logger
{
  public:
  // Prevent copying loggers
  private:
    logger(const logger&)
    {}

    logger& operator =(const logger&)
    {
      return *this;
    }

  protected:
    /// \brief Stream that is printed to internally
    /// Collects the full debug message that we are currently printing.
    std::ostringstream m_os;

    /// \brief The loglevel of the current message
    log_level_t m_level;

    /// \brief The message hint of the current message
    std::string m_hint;

    /// \brief Timestamp of the current message
    time_t m_timestamp;

    /// \brief Output policies
    static
    std::set<output_policy*>& output_policies()
    {
      static std::set<output_policy*> m_output_policies = initialise_output_policies();
      return m_output_policies;
    }

    /// \brief Mapping of message hint to loglevel. This allows a finegrained
    /// control of log messages to log levels. It can e.g. be set that for some
    /// message hint all messages up to debug level are printed, whereas for other
    /// message hints no messages are printed at all.
    static
    std::map<std::string, log_level_t>& hint_to_level()
    {
      static std::map<std::string, log_level_t> m_hint_to_level;
      return m_hint_to_level;
    }

    /// \brief The default log level that is used if no specific log level has
    /// been set.
    static
    log_level_t default_reporting_level()
    {
      std::map<std::string, log_level_t>::const_iterator i = hint_to_level().find(default_hint());
      if(i != hint_to_level().end())
      {
        return i->second;
      }
      else
      {
        return info;
      }
    }

  public:
    /// \brief Default constructor
    logger()
    {}

    /// \brief Destructor; flushes output.
    /// Flushing during destruction is important to confer thread safety to the
    /// logging mechanism. Requires that output performs output in an atomic way.
    ~logger()
    {
      for(std::set<output_policy*>::iterator i = output_policies().begin(); i != output_policies().end(); ++i)
      {
        (*i)->output(m_level, m_hint, m_timestamp, m_os.str());
      }
    }

    /// \brief Default hint (empty)
    static std::string default_hint()
    {
      static std::string default_hint;
      return default_hint;
    }

    /// \brief Register output policy
    static
    void register_output_policy(output_policy& policy)
    {
      output_policies().insert(&policy);
    }

    /// \brief Unregister output policy
    static
    void unregister_output_policy(output_policy& policy)
    {
      std::set<output_policy*>::iterator i = output_policies().find(&policy);
      if(i != output_policies().end())
      {
        output_policies().erase(i);
      }
    }

    /// \brief Clear all output policies
    static
    void clear_output_policies()
    {
      output_policies().clear();
    }

    /// \brief Set reporting level
    /// \param[in] level Log level
    /// \param[in] hint The hint for which to set log level
    static
    void set_reporting_level(const log_level_t level, const std::string& hint = default_hint())
    {
      hint_to_level()[hint] = level;
    }

    /// \brief Get reporting level
    /// \param[in] hint The hint for which to get log level
    static
    log_level_t get_reporting_level(const std::string& hint = default_hint())
    {
      std::map<std::string, log_level_t>::const_iterator i = hint_to_level().find(hint);
      if(i != hint_to_level().end())
      {
        return i->second;
      }
      else
      {
        return default_reporting_level();
      }
    }

    /// \brief Clear reporting level
    /// \param hint Reset the log level for hint
    static
    void clear_reporting_level(const std::string& hint)
    {
      hint_to_level().erase(hint);
    }

    /// Get access to the stream provided by the logger.
    /// \param[in] l Log level for the stream
    /// \param[in] hint The hint for which the stream has to be provided.
    std::ostringstream& get(const log_level_t l, const std::string& hint = default_hint())
    {
      m_level = l;
      m_hint = hint;
      std::time(&m_timestamp);
      return m_os;
    }
};

class formatter_interface
{
public:
  /// \brief Format msg,
  /// \param[in] level The log level of the message
  /// \param[in] hint The hint provided for the message
  /// \param[in] timestamp The timestamp of the log message
  /// \param[in] msg The message to be formatted
  /// \return The formatted message (\a msg)
  static std::string format(const log_level_t /*level*/, const std::string& /*hint*/, const time_t /*timestamp*/, const std::string& msg)
  {
    return msg;
  }
};

/// \brief Mixin that takes care of formatting of a message.
///
/// In this case, the formatter
class formatter: public formatter_interface
{
protected:
  /// \brief Records whether the last message that was printed ended with
  ///        a new line.
  static
  bool& last_message_ended_with_newline()
  {
    static bool m_last_message_ended_with_newline = true;
    return m_last_message_ended_with_newline;
  }

  static
  bool& last_message_was_status()
  {
    static bool m_last_message_was_status = false;
    return m_last_message_was_status;
  }

  static
  std::string& last_hint()
  {
    static std::string m_last_hint;
    return m_last_hint;
  }

  static
  size_t& caret_pos()
  {
    static size_t m_caret_pos = 0;
    return m_caret_pos;
  }

  static
  size_t& last_caret_pos()
  {
    static size_t m_last_caret_pos = 0;
    return m_last_caret_pos;
  }

public:
  /// \brief Prefix each line in s with some extra information.
  /// The things that are added are:
  /// - current time
  /// - hint
  /// - log level
  /// - indentation
  static std::string format(const log_level_t level, const std::string& hint, const time_t timestamp, const std::string& msg);
};

/// \brief File output class.
///
/// Provides facilities to output to a file. By default output is sent to stderr.
class file_output: public output_policy
{
  protected:
    /// \brief Map hints to streams
    /// This allows messages with different hints to be written to different output
    /// streams.
    static
    std::map<std::string, FILE*>& hint_to_stream()
    {
      static std::map<std::string, FILE*> m_hint_to_stream;
      return m_hint_to_stream;
    }

    /// \brief Gets a stream handle for hint
    /// \param[in] hint Hint for which to provide a stream handle.
    FILE* get_stream(const std::string& hint)
    {
      std::map<std::string, FILE*>::iterator i = hint_to_stream().find(hint);
      if(i == hint_to_stream().end())
      {
        i = hint_to_stream().find(logger::default_hint());
      }
      if (i == hint_to_stream().end())
      {
        return stderr;
      }
      else
      {
        return i->second;
      }
    }

  public:
    file_output()
    {}

    virtual ~file_output()
    {}

    /// \brief Set stream handle for a hint
    /// \param[in] stream A file handle
    /// \param[in] hint The hint for which to set the handle to stream.
    static
    void set_stream(FILE* stream, const std::string& hint = logger::default_hint())
    {
      hint_to_stream()[hint] = stream;
    }

    /// \overload
    /// Output message to stream.
    /// \param[in] msg The message to be printed
    /// \param[in] hint The hint of the stream to which we print.
    /// This uses fprintf (and not e.g. <<) because fprintf is guaranteed to be
    /// atomic.
    virtual void output(const log_level_t level, const std::string& hint, const time_t timestamp, const std::string& msg)
    {
      FILE* p_stream = get_stream(hint);
      if (!p_stream)
      {
        return;
      }

      fprintf(p_stream, "%s", formatter::format(level, hint, timestamp, msg).c_str());
      fflush(p_stream);
    }
};

/// \brief Output policy that wraps a function pointer to do the actual output
///
/// \deprecated Instead of using this output policy, use a custom class
/// inheriting from output_policy.
template<typename Formatter>
class function_pointer_output: public output_policy
{

public:
  /// \brief Type for message distinction (by purpose).
  /// Should only be used for custom message handlers.
  enum message_t
  {
    msg_notice,
    msg_warning,
    msg_error
  };

  /// \brief Type for function pointer for a custom message printing routine
  /// \deprecated
  /// provided for backward compatibility with gs*Msg
  typedef void (*custom_message_handler_t)(message_t, const char*);

  /// \brief Pointer that contains a custom message handler.
  custom_message_handler_t m_handler;

  /// \brief Formatting
  formatter_interface m_formatter;

protected:
  /// \brief Conversion of log level to message type
  message_t to_message_type(const log_level_t level) const
  {
    if (level <= error)
    {
      return msg_error;
    }
    else if (level <= warning)
    {
      return msg_warning;
    }
    else
    {
      return msg_notice;
    }
  }

public:

  function_pointer_output()
    : m_handler(NULL)
  {}

  function_pointer_output(custom_message_handler_t handler)
    : m_handler(handler)
  {}

  void set_custom_message_handler(custom_message_handler_t handler)
  {
    m_handler = handler;
  }

  virtual void output(const log_level_t level, const std::string& hint, const time_t timestamp, const std::string& msg)
  {
    m_handler(to_message_type(level), Formatter::format(level, hint, timestamp, msg).c_str());
  }
};

/// \brief The default output policy used by the logger
inline
output_policy& default_output_policy()
{
  static file_output m_default = file_output();
  return m_default;
}

/// \brief Initialise the output policies. This returns the singleton set
///        containing the default output policy.
inline
std::set<output_policy*> initialise_output_policies()
{
  std::set<output_policy*> result;
  result.insert(&default_output_policy());
  return result;
}

/// Unless otherwise specified, we compile away all debug messages that have
/// a log level greater than MCRL2_MAX_LOG_LEVEL.
#ifndef CPPLOG_MAX_LOG_LEVEL
#define CPPLOG_MAX_LOG_LEVEL cpplogging::debug
#endif

/// log(level) provides the function used to log. It performs two
/// optimisations:
/// - the first comparison (level > MAX_LOG_LEVEL), compares two constants
///   during compile time. The compiler will not create any code if (level > MAX_LOG_LEVEL).
/// - the second comparison compares two constants at runtime. This check makes
///   sure that the arguments to log(level) will not be evaluated if level > file_logger::reporting_level().
/// In all other cases this macro provides a stream that can be printed to.
// Note that the macro uses the dirty preprocessor token concatenation. For a
// description, see e.g. http://en.wikipedia.org/wiki/C_preprocessor#Token_concatenation
// (accessed 7/4/2011)
// We also use the facilities to provide a variable number of arguments to a macro, in order
// to allow mCRL2log(level) as well as mCRL2log(level, "hint")
#define cpplog(level, ...) \
if ((level) > CPPLOG_MAX_LOG_LEVEL) ; \
else if ((level) > (cpplogging::logger::get_reporting_level(__VA_ARGS__))) ; \
else cpplogging::logger().get(level, ##__VA_ARGS__)

#define cpplogEnabled(level, ...) \
(((level) <= CPPLOG_MAX_LOG_LEVEL) && ((level) <= (cpplogging::logger::get_reporting_level(__VA_ARGS__))))

  } // namespace cpplogging
#endif /* LOGGING_LOGGER_H */
