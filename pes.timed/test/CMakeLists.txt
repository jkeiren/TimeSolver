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

# The gtest/gtest_main targets carry header search path
# dependencies automatically when using CMake 2.8.11 or
# later. Otherwise we have to add them here ourselves.
if (CMAKE_VERSION VERSION_LESS 2.8.11)
  include_directories("${gtest_SOURCE_DIR}/include")
endif()


include(GoogleTest)
set(PROJECT_TEST_NAME ${PROJECT_NAME}_test)

# file(GLOB_RECURSE TEST_SRC_FILES .
#   *.cc)
# message(STATUS "Test case source files: " ${TEST_SRC_FILES})

# add_executable(${PROJECT_TEST_NAME} ${TEST_SRC_FILES})
# target_link_libraries(${PROJECT_TEST_NAME} gtest_main parse ExprNode cpplogger)

add_executable(parsetest parsetest.cc)
add_executable(dbmtest dbmtest.cc)
add_executable(dbmlisttest dbmlisttest.cc)
add_executable(prooftest prooftest.cc)
target_link_libraries(parsetest gtest_main parse cpplogger)
target_link_libraries(dbmtest gtest_main ExprNode cpplogger)
target_link_libraries(dbmlisttest gtest_main ExprNode cpplogger)
target_link_libraries(prooftest gtest_main parse ExprNode cpplogger)

gtest_discover_tests(parsetest)
gtest_discover_tests(dbmtest)
gtest_discover_tests(dbmlisttest)
gtest_discover_tests(prooftest)