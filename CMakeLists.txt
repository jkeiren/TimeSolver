cmake_minimum_required(VERSION 3.10)
project (timesolver)

enable_testing()

# Used in testing using the parser
add_definitions("-DEXAMPLES_DIR=${CMAKE_SOURCE_DIR}/examples")

# Recursive
add_subdirectory("pes.timed")

add_custom_target(tool-test 
  COMMAND "${CMAKE_SOURCE_DIR}/TATest.py"
  DEPENDS timesolver-ta)
add_custom_target(tool-test-examples
  COMMAND "${CMAKE_SOURCE_DIR}/TATest.py -xn"
  DEPENDS timesolver-ta)