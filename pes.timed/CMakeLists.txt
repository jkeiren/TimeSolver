set (CMAKE_CXX_STANDARD 11)
set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -O -Wall")
set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -O -Wall -Wextra")

# 	# Stack size set to 4GB for Mac, since terminal hard limit is 64MB
# 	# My machine has 16GB of RAM
# 	# This number is the number of bytes in Hex
if(APPLE)
  set (CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,-stack_size,200000000")
endif()

add_subdirectory(external/cpplogging)

find_package(BISON)
find_package(FLEX)

BISON_TARGET(PesParser pes.y ${CMAKE_CURRENT_BINARY_DIR}/pes.tab.cc)
FLEX_TARGET(PesScanner pes.l ${CMAKE_CURRENT_BINARY_DIR}/pes.lex.cc)
ADD_FLEX_BISON_DEPENDENCY(PesScanner PesParser)

include_directories(${CMAKE_CURRENT_BINARY_DIR}
  ${CMAKE_CURRENT_SOURCE_DIR}
  external/cpplogging/include)

add_library(ExprNode ExprNode.cc)
add_library(parse parse.cc pes.lex.cc pes.tab.cc)

add_executable(timesolver-ta
  timesolver-ta.cc
  ${BISON_PesParser_OUTPUTS}
  ${FLEX_PesScanner_OUTPUTS}
  )
target_link_libraries(timesolver-ta cpplogger ExprNode parse)

install (TARGETS timesolver-ta DESTINATION bin)

add_subdirectory(test)

find_package(Doxygen)
doxygen_add_docs(doxygen 
  ${PROJECT_SOURCE_DIR}
  COMMENT "Generate doxygen documentation")
