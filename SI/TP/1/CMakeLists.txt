# CMake entry point
cmake_minimum_required (VERSION 2.6)
project(polytech_ricm4_tp1)

find_package(OpenGL REQUIRED)

# Compile external dependencies 
#add_subdirectory (external)
add_subdirectory (./external ./external/build)

include_directories(src/)
include_directories(
	./external/glfw-2.7.6/include/
	./external/glm-0.9.4.0/
	./external/glew-1.9.0/include/
)


set(ALL_LIBS
	GLFW_276
	GLEW_190
)

add_definitions(
	-DTW_STATIC
	-DTW_NO_LIB_PRAGMA
	-DTW_NO_DIRECT3D
	-DGLEW_STATIC
	-D_CRT_SECURE_NO_WARNINGS
)

file(
	GLOB_RECURSE
	source_files
        src/*.cpp
        src/*.hpp
)

add_executable(polytech_ricm4_tp1 ${source_files} )
target_link_libraries(polytech_ricm4_tp1 ${ALL_LIBS})

