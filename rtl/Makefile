CC      = gcc
CFLAGS  = -O2 -Wall -Wextra -std=c11

SRC_DIR = src/main/c
OBJ_DIR = target
LIB     = $(OBJ_DIR)/blaise_rtl.a

# Where the compiler binary lives — install copies the RTL there so the
# driver finds it automatically next to itself.
COMPILER_BIN = ../compiler/target/bin

SRCS = $(SRC_DIR)/blaise_arc.c \
       $(SRC_DIR)/blaise_exc.c
OBJS = $(patsubst $(SRC_DIR)/%.c,$(OBJ_DIR)/%.o,$(SRCS))

.PHONY: all install clean

all: $(LIB)

$(LIB): $(OBJS)
	ar rcs $@ $^

$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c
	@mkdir -p $(OBJ_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

install: $(LIB)
	@mkdir -p $(COMPILER_BIN)
	cp $(LIB) $(COMPILER_BIN)/blaise_rtl.a
	@echo "Installed blaise_rtl.a → $(COMPILER_BIN)/blaise_rtl.a"

clean:
	rm -f $(OBJ_DIR)/*.o $(LIB)
