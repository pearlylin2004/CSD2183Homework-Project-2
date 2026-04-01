CXX = g++
CXXFLAGS = -std=c++17 -O2 -Wall -Wextra

SRCS = Project_HW2/source/main.cpp
TARGET = simplify

$(TARGET): $(SRCS)
	$(CXX) $(CXXFLAGS) -o $(TARGET) $(SRCS)

clean:
	rm -f $(TARGET)
	