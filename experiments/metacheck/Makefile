PKG = MetaCheck
include $(LEAN4_S1_MK)
all: metacheck

MetaCheckEXE=metacheck
LEAN4_PATH=$(LEAN4_S1_LIB)

metacheck: $(BIN_OUT)/test
	cp $(BIN_OUT)/test $(MetaCheckEXE)

$(BIN_OUT)/test: $(LIB_OUT)/libMetaCheck.a $(CPP_OBJS) | $(BIN_OUT)
	c++ -rdynamic -o $@ $^ `leanc --print-ldflags`
