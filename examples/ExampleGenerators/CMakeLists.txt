cmake_minimum_required(VERSION 3.5.0)


include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Build the actual executable
add_executable(csma csma.cpp)
add_executable(fddi fddi.cpp)
add_executable(fischer fischer.cpp)
add_executable(grc grc.cpp)
add_executable(leader leader.cpp)
add_executable(pathos pathos.cpp)
