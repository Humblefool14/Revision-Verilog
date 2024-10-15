# Check if Homebrew GCC exists and get its version
BREWGCC := $(shell brew --prefix gcc)/bin/g++-*
#ifneq ($(wildcard $(BREWGCC)),)
#    CXX := $(wildcard $(BREWGCC))
#else
    CXX := g++
#endif

OPENMP_PATH := $(shell brew --prefix libomp)
CXXFLAGS := -O3 -std=c++11 -Xpreprocessor -fopenmp -lomp
LDFLAGS := -L$(OPENMP_PATH)/lib
CPPFLAGS := -I$(OPENMP_PATH)/include

TARGET := prefix_scan
SOURCE := prefix_scan.cpp

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CXX) $(CXXFLAGS) $(CPPFLAGS) $(LDFLAGS) $< -o $@

clean:
	rm -f $(TARGET)

.PHONY: all clean