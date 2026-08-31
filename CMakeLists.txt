cmake_minimum_required(VERSION 3.18)

project(darm_monitor_system C CXX ASM)

# Load CAmkES build system macros and seL4 toolchain configuration
find_package(camkes REQUIRED)
find_package(seL4 REQUIRED)

# Locate Lean toolchain paths via elan
execute_process(
    COMMAND elan which lean
    OUTPUT_VARIABLE LEAN_BIN_PATH
    OUTPUT_STRIP_TRAILING_WHITESPACE
)
if(LEAN_BIN_PATH)
    get_filename_component(LEAN_ROOT "${LEAN_BIN_PATH}" DIRECTORY)
    get_filename_component(LEAN_HOME "${LEAN_ROOT}" DIRECTORY)
else()
    set(LEAN_HOME "$ENV{HOME}/.elan/toolchains/stable")
endif()

set(LEAN_INCLUDE_DIR "${LEAN_HOME}/include")
set(LEAN_LIB_DIR "${LEAN_HOME}/lib/lean")

# Custom target to build Lean proof towers and compile C emissions before CMake links
add_custom_target(lake_build ALL
    COMMAND lake build
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
    COMMENT "Building verified Lean 4 proof towers and C bindings..."
)

# Include directories across targets
include_directories(include ${LEAN_INCLUDE_DIR})

# Declare CAmkES component sources and executable targets
DeclareCAmkESComponent(DarmMonitor
    SOURCES camkes/darm_monitor.c tests/test_darm_shim.c
    INCLUDES include ${LEAN_INCLUDE_DIR}
)

# Ensure Lake finishes building before linking DarmMonitor component
add_dependencies(DarmMonitor lake_build)

# Link compiled Lean static library and Lean runtime
target_link_libraries(DarmMonitor
    PRIVATE
        ${CMAKE_SOURCE_DIR}/.lake/build/lib/libDarmMonitor.a
        ${LEAN_LIB_DIR}/libleanc.a
)

# Register static assembly target topology
DeclareCAmkESRoot(camkes/darm_monitor.camkes)
