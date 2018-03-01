cmake_minimum_required(VERSION 3.10)

# Download and unpack googletest at configure time
configure_file(CMakeLists.txt.in ${CMAKE_BINARY_DIR}/googletest-download/CMakeLists.txt)
execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
if(result)
  message(FATAL_ERROR "CMake step for googletest failed: ${result}")
endif()
execute_process(COMMAND ${CMAKE_COMMAND} --build .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_BINARY_DIR}/googletest-download )
if(result)
  message(FATAL_ERROR "Build step for googletest failed: ${result}")
endif()

# Prevent overriding the parent project's compiler/linker
# settings on Windows
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)

# Add googletest directly to our build. This defines
# the gtest and gtest_main targets.
add_subdirectory(${CMAKE_BINARY_DIR}/googletest-src
                 ${CMAKE_BINARY_DIR}/googletest-build
                 EXCLUDE_FROM_ALL)

# Now, include the GoogleTest features, so that we can discover all tests
# defined in a googletest suit.
include(GoogleTest)

# Add all .cc files in this directory as tests.
file(GLOB_RECURSE TEST_SRC_FILES . *.cc)
foreach(file ${TEST_SRC_FILES})
  get_filename_component(TESTNAME ${file} NAME)
  add_executable(${TESTNAME} ${file})
  target_link_libraries(${TESTNAME} gtest_main parse ExprNode cpplogger)
  gtest_discover_tests(${TESTNAME})
endforeach()

