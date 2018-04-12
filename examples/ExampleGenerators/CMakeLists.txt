cmake_minimum_required(VERSION 3.5.0)


include_directories(${CMAKE_CURRENT_SOURCE_DIR})

# Build the actual executable
add_executable(csma csma.cc)
add_executable(fddi fddi.cc)
add_executable(fischer fischer.cc)
add_executable(grc grc.cc)
add_executable(leader leader.cc)
add_executable(pathos pathos.cc)

