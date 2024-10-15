# Compiler
CXX = g++

# Compiler flags
CXXFLAGS = -fopenmp -O3 -std=c++11

# Source file
SOURCE = parallel_prefix_sum.cpp

# Output executable
TARGET = prefix_sum

# Default target
all: $(TARGET)

# Rule to build the executable
$(TARGET): $(SOURCE)
	$(CXX) $(CXXFLAGS) $(SOURCE) -o $(TARGET)

# Clean rule
clean:
	rm -f $(TARGET)

# Phony targets
.PHONY: all clean