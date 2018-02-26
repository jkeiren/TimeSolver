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

# Find all examples
file(GLOB_RECURSE EXAMPLE_FILES "${PROJECT_SOURCE_DIR}/examples/*.in")

foreach(file ${EXAMPLE_FILES})
  string(REPLACE "${PROJECT_SOURCE_DIR}/examples/" "" TESTNAME ${file})
  string(REGEX MATCH "(FISCHER-[5-9])|(GRC-[5-9])|(LEADER-[5-9])|Train[4-9]" SKIP "${TESTNAME}" )
  set(TEST_COMMAND "${PROJECT_BINARY_DIR}/pes.timed/timesolver-ta")
  if(NOT SKIP)
    message(STATUS "NO")
    string(REGEX MATCH "GRC" NODIFF "${TESTNAME}")
    if(NODEBUG)
      set(TEST_COMMAND "${TEST_COMMAND} --nodebug")
    endif()

    add_test(tooltest-${TESTNAME} "${PROJECT_SOURCE_DIR}/TATest-one.py" ${TEST_COMMAND} ${file} DEPENDS timesolver-ta)
  endif()
endforeach()
