cmake_minimum_required(VERSION 3.14)

project(CCAnrWithPredict)

set (CMAKE_CXX_STANDARD 11)

find_package(PythonInterp 3 REQUIRED)
find_package(Python REQUIRED Development NumPy)
find_package(PythonLibs 3 REQUIRED)
find_package(Boost REQUIRED COMPONENTS python${PYTHON_MAJOR_VERSION}${PYTHON_MINOR_VERSION} numpy${PYTHON_MAJOR_VERSION}${PYTHON_MINOR_VERSION} program_options)

option(USE_PREDICT "use predict in solver" ON)
configure_file(sat_defines.hpp.in sat_defines.hpp)

include_directories(${Python3_INCLUDE_DIRS} ${Python3_NumPy_INCLUDE_DIRS} ${Boost_INCLUDE_DIRS} ${CMAKE_BINARY_DIR})
link_directories(${Python3_INCLUDE_DIRS} ${Boost_LIBRARY_DIRS})

if(MSVC)
    if(CMAKE_CXX_FLAGS MATCHES "/W[0-4]")
        string(REGEX REPLACE "/W[0-4]" "/W4" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
    else()
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /W4")
    endif()
elseif(CMAKE_COMPILER_IS_GNUCC OR CMAKE_COMPILER_IS_GNUCXX)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wno-long-long -pedantic -O3")
endif()

file(GLOB CCAnrWithPredict_SRC
    "*.hpp"
    "*.cpp"
)

add_executable(CCAnrWithPredict
    ${CCAnrWithPredict_SRC})

target_link_libraries(CCAnrWithPredict
    Python::Python
    Python::NumPy
    Boost::program_options)
