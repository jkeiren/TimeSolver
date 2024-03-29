cmake_minimum_required(VERSION 3.5.0)

set (CMAKE_CXX_STANDARD 11)
set (CMAKE_CXX_STANDARD_REQUIRED ON)
set (CMAKE_CXX_EXTENSIONS OFF)
set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -Wpedantic -Wno-gnu-zero-variadic-macro-arguments -Wno-deprecated-register")

set(CMAKE_CXX_FLAGS_RELEASE "-O2 -DNDEBUG") #  -march=native -mtune=native
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DTIMESOLVER_DEBUG")

if (NOT DEFINED TIMESOLVER_MAX_LOG_LEVEL)
  set (TIMESOLVER_MAX_LOG_LEVEL "debug" CACHE STRING "The maximum log level to enable at compile time.")
endif()

add_definitions("-DCPPLOG_MAX_LOG_LEVEL=cpplogging::${TIMESOLVER_MAX_LOG_LEVEL}")

if(APPLE)
  if (NOT DEFINED TIMESOLVER_OSX_STACK_SIZE)
    # Stack size set to 4GB for Mac, since terminal hard limit is 64MB
    # This number is the number of bytes in Hex
    set (TIMESOLVER_OSX_STACK_SIZE "200000000" CACHE STRING "Maximum stack size to allow on MacOS, in number of bytes in hexadecimal (200000000 equals 4GB).")
  endif()
  set (CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,-stack_size,${TIMESOLVER_OSX_STACK_SIZE}")
endif()

include(version_string.cmake)
include(AddSanitizer.cmake)

# Include the logging library
add_subdirectory(external/cpplogging)

# Generate lexer and parser
find_package(BISON)
find_package(FLEX)
BISON_TARGET(PesParser pes.y ${CMAKE_CURRENT_BINARY_DIR}/pes.tab.cpp)
FLEX_TARGET(PesScanner pes.l ${CMAKE_CURRENT_BINARY_DIR}/pes.lex.cpp DEFINES_FILE pes.lex.hh)
ADD_FLEX_BISON_DEPENDENCY(PesScanner PesParser)

include_directories(${CMAKE_CURRENT_BINARY_DIR} # for lexer/parser
  ${CMAKE_CURRENT_SOURCE_DIR}
  external/cpplogging/include)

# Build two libraries for the sake of unit testing
add_library(ExprNode ExprNode.cpp)
add_library(parse parse.cpp ${CMAKE_CURRENT_BINARY_DIR}/pes.lex.cpp ${CMAKE_CURRENT_BINARY_DIR}/pes.tab.cpp)

# Build the actual executable
add_executable(timesolver-ta
  timesolver-ta.cpp
  ${BISON_PesParser_OUTPUTS}
  ${FLEX_PesScanner_OUTPUTS}
  )
# Link executable
target_link_libraries(timesolver-ta cpplogger ExprNode parse)

# Make install by default installs to the bin directory.
install (TARGETS timesolver-ta DESTINATION bin)

# Enable unit-testing (conditionally)
if(${CMAKE_VERSION} VERSION_LESS "3.10")
  message(WARNING "Not building unit tests; consider switching to CMake 3.10 or newer")
else()
  add_subdirectory(test)
endif()

# Detect doxygen. If doxygen is available, allow generating doxygen documentation.
if(${CMAKE_VERSION} VERSION_LESS "3.9.6")
  message(WARNING "Not generating Doxygen documentation; consider switching to CMake 3.9.6 or newer")
else()
  find_package(Doxygen)
  if(${DOXYGEN_FOUND})
    doxygen_add_docs(doxygen
      ${PROJECT_SOURCE_DIR}
      COMMENT "Generate doxygen documentation")
  endif()
endif()
