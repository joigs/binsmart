cmake_minimum_required(VERSION 3.16)
project(binsmart LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Ajusta optimización a gusto
if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

add_executable(original src/original.cpp
        src/original.cpp)

# Flags razonables (opcional)
if (MSVC)
    target_compile_options(original PRIVATE /O2 /permissive-)
else()
    target_compile_options(original PRIVATE -O3 -march=native -Wall -Wextra -Wpedantic)
endif()
