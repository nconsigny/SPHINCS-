# JARDIN-Keccak-128-24 one-shot signer

CC      ?= cc
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -std=c99 -I.

SRC = address.c \
      fors.c \
      hash_keccak.c \
      keccak.c \
      merkle.c \
      randombytes.c \
      sign.c \
      thash_keccak.c \
      utils.c \
      utilsx1.c \
      wots.c \
      wotsx1.c \
      main.c

OBJ = $(SRC:.c=.o)
BIN = jardin-keccak-128-24

all: $(BIN)

$(BIN): $(OBJ)
	$(CC) $(CFLAGS) -o $@ $(OBJ)

# Header dependency tracking. Without it, editing a header — params.h holds the
# compile-time PARAMETER SET — leaves stale .o files while `make` reports
# "Nothing to be done", so the binary silently stops matching its sources.
# Kept out of CFLAGS so a caller override (CI builds reduced params with
# `make CFLAGS=...`) cannot drop it.
DEPFLAGS = -MMD -MP

%.o: %.c
	$(CC) $(CFLAGS) $(DEPFLAGS) -c -o $@ $<

-include $(OBJ:.o=.d)

clean:
	rm -f $(BIN) *.o *.d

.PHONY: all clean
