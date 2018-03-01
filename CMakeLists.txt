cmake_minimum_required(VERSION 3.0.2)
project (timesolver)

# Allow generating tests
enable_testing()

# Add definition used in unit testing.
add_definitions("-DEXAMPLES_DIR=${CMAKE_SOURCE_DIR}/examples")

# Recursively build the tool
add_subdirectory("pes.timed")

# Add tool tests, running all examples
# First, let's find all examples
file(GLOB_RECURSE EXAMPLE_FILES "${PROJECT_SOURCE_DIR}/examples/*.in")

# For each example we add a test case.
foreach(file ${EXAMPLE_FILES})
  string(REPLACE "${PROJECT_SOURCE_DIR}/examples/" "" TESTNAME ${file})
  string(REGEX MATCH "(FISCHER-[5-9])|(GRC-[5-9])|(LEADER-[5-9])|Train[4-9]" SKIP "${TESTNAME}" )
  if(NOT SKIP)
    string(REGEX MATCH "GRC-4" NODEBUG "${TESTNAME}")
    if(NODEBUG)
      set(NODEBUG_ARG --nodebug)
    else()
      unset(NODEBUG_ARG)
    endif()

    add_test(tooltest-${TESTNAME}
             ${PROJECT_SOURCE_DIR}/TATest-one.py -d ${NODEBUG_ARG}
             ${PROJECT_BINARY_DIR}/pes.timed/timesolver-ta
             ${file}
             DEPENDS timesolver-ta
             TIMEOUT 420)
  endif()
endforeach()
