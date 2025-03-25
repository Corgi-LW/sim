
cmake_minimum_required(VERSION 3.10)
project(trans)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

# Find OpenSSL for SHA256
find_package(OpenSSL REQUIRED)

# Add include directory
include_directories(${PROJECT_SOURCE_DIR}/include)

# Add executable
add_executable(trans main.cpp)

# Link OpenSSL
target_link_libraries(trans OpenSSL::SSL OpenSSL::Crypto)



