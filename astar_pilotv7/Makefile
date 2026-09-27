
PILOT_NAME = astar_pilotv7

CC     = gcc
CFLAGS = -ansi -pedantic -Wall -Wextra -Wpedantic -g
LDLIBS = -lm

SANITIZE = off
ifeq ($(SANITIZE),on)
CFLAGS += -fsanitize=address
endif

DRIVERS_PATH = ../drivers

SRCS = astar_pilotv7.c follow_line.c

.PHONY: all clean distclean install

all: $(PILOT_NAME)

install: $(DRIVERS_PATH)/$(PILOT_NAME)

$(DRIVERS_PATH)/$(PILOT_NAME): $(PILOT_NAME)
	cp $(PILOT_NAME) $(DRIVERS_PATH)

$(PILOT_NAME): $(SRCS)
	$(CC) $(CFLAGS) -o $@ $^ $(LDLIBS)

distclean: clean
	rm -f $(PILOT_NAME)
	rm -rf $(PILOT_NAME).dSYM

clean:
	rm -f *~ *.o
