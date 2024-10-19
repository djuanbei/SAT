
cmake_minimum_required(VERSION 3.5)
project(SAT)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)


add_library(${PROJECT_NAME} src/Solver.h src/Solver.cpp)


add_executable(main Main.cpp)

target_link_libraries(main ${PROJECT_NAME})









