cmake_minimum_required(VERSION 3.14)

project(satutils)

set (CMAKE_CXX_STANDARD 11)

find_package(PythonInterp 3 REQUIRED)
find_package(Python REQUIRED Development NumPy)
find_package(PythonLibs 3 REQUIRED)
find_package(Boost REQUIRED COMPONENTS python${PYTHON_MAJOR_VERSION}${PYTHON_MINOR_VERSION} numpy${PYTHON_MAJOR_VERSION}${PYTHON_MINOR_VERSION})

message(STATUS "PYTHON_LIBRARIES = ${PYTHON_LIBRARIES}")
message(STATUS "PYTHON_EXECUTABLE = ${PYTHON_EXECUTABLE}")
message(STATUS "PYTHON_INCLUDE_DIRS = ${PYTHON_INCLUDE_DIRS}")
message(STATUS "Boost_LIBRARIES = ${Boost_LIBRARIES}")
message(STATUS "PYTHON_VERSION_SUFFIX = ${PYTHON_VERSION_SUFFIX}")

if(MSVC)
    if(CMAKE_CXX_FLAGS MATCHES "/W[0-4]")
        string(REGEX REPLACE "/W[0-4]" "/W4" CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS}")
    else()
        set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} /W4")
    endif()
elseif(CMAKE_COMPILER_IS_GNUCC OR CMAKE_COMPILER_IS_GNUCXX)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wno-long-long -pedantic -ggdb")
endif()

file(GLOB SatUtils_SRC
    "*.hpp"
    "*.cpp"
    "*.h"
)

include_directories(${Boost_INCLUDE_DIRS} ${PYTHON_INCLUDE_DIRS})

PYTHON_ADD_MODULE(satutils ${SatUtils_SRC})
target_link_libraries(satutils
    Boost::python${PYTHON_MAJOR_VERSION}${PYTHON_MINOR_VERSION}
    Boost::numpy${PYTHON_MAJOR_VERSION}${PYTHON_MINOR_VERSION})
