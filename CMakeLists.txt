cmake_minimum_required(VERSION 3.18)

project(darm_monitor_system C CXX ASM)

# Load CAmkES build system macros and seL4 toolchain configuration
find_package(camkes REQUIRED)
find_package(seL4 REQUIRED)

# Include C-ABI header path across component modules
include_directories(include)

# Declare component sources and executable targets
DeclareCAmkESComponent(DarmMonitor
    SOURCES camkes/darm_monitor.c tests/test_darm_shim.c
    INCLUDES include
)

# Register static assembly target topology
DeclareCAmkESRoot(camkes/darm_monitor.camkes)
