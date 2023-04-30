CXX_FLAGS		:= -O2 -Wall -c -fPIC
CXX_LD_FLAGS		:= -shared -lcurl -ljsoncpp -lazguestattestation

ATTESTATION_LIB		= libsev_attestation.so
ATTESTATION_SRCS	= $(wildcard ./*.cc)
ATTESTATION_OBJS	= $(patsubst %.cc, %.o, $(ATTESTATION_SRCS))

.phony: clean

$(ATTESTATION_LIB): $(ATTESTATION_OBJS)
	$(CXX) $(CXX_LD_FLAGS) -o $@ $^

%.o: %.cc
	$(CXX) $(CXX_FLAGS) -o $@ $^

clean:
	@rm -f *.so *.o
