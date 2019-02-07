.POSIX:

.SUFFIXES:
.SUFFIXES: .c .cpp .o .d .fc

include config.mk

# Sources
CXXSRC = $(shell find src -name "*.cpp")
CCSRC  = $(shell find src -name "*.c")

# Objects
CXXOBJ = $(CXXSRC:.cpp=.o)
CCOBJ  = $(CCSRC:.c=.o)
OBJ    = $(CXXOBJ) $(CCOBJ)

# Proof results
FCSRC  = $(CCSRC:.c=.fc)

# Dependency files
DEPS   = $(OBJ:.o=.d)

all: prove $(NAME)

# Compilation
.cpp.o:
	$(CXX) $(COMMON_FLAGS) $(CXXFLAGS) -MMD -c -o $@ $<
.c.o:
	$(CC) $(COMMON_FLAGS) $(CCFLAGS) -MMD -c -o $@ $<

# Proving
.c.fc:
	frama-c -wp -wp-rte $< > $@

# Linking
$(NAME): $(OBJ)
	#$(CXX) -o $@ $(OBJ) $(LDFLAGS)

prove: $(FCSRC)

# Dependencies
-include $(DEPS)

debug: CXXFLAGS += -DDEBUG -g
debug: CCFLAGS  += -DDEBUG -g
debug: $(NAME)

clean:
	rm -f $(NAME) $(NAME).asm $(OBJ) $(DEPS) $(FCSRC)

run: $(NAME)
	./$(NAME)

dump: $(NAME)
	objdump -dC $(NAME) > $(NAME).asm

.PHONY: all clean
