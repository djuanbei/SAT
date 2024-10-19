
cmake_minimum_required(VERSION 3.5)
project(SAT)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

option(REQUIRE_GTEST "Require uses googletest UT framework" ON)
if (REQUIRE_GTEST)
    include(cmake/gtest_config.cmake)
    enable_testing()
endif ()


add_library(${PROJECT_NAME} src/Solver.h src/Solver.cpp)


add_executable(main Main.cpp)

target_link_libraries(main ${PROJECT_NAME})


if (REQUIRE_GTEST)

    add_executable(SolverTest src/SolverTest.cpp)

    target_link_libraries(SolverTest PRIVATE ${PROJECT_NAME} gtest_main)

endif ()







