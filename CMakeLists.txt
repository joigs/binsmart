cmake_minimum_required(VERSION 3.16)
project(binsmart LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Encuentra la librería de hilos del sistema (pthread en Linux)
find_package(Threads REQUIRED)  # <- AGREGAR ESTO

if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

add_library(tm STATIC src/tm.cpp)
target_include_directories(tm PUBLIC src)

add_executable(original src/original.cpp)
target_link_libraries(original PRIVATE tm)

add_executable(inversa src/inversa.cpp)
target_link_libraries(inversa PRIVATE tm)

add_executable(findH src/findH.cpp)
# Linkea tm Y TAMBIÉN Threads::Threads
target_link_libraries(findH PRIVATE tm Threads::Threads) # <- MODIFICAR ESTO