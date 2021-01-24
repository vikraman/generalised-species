AGDA_SRCS = $(shell find . -type f -name '*.agda' -not -wholename './old/*')
AGDA_BINS = $(subst .agda,.agdai,$(AGDA_SRCS))

all: $(AGDA_BINS)

%.agdai: %.agda
	agda $<
