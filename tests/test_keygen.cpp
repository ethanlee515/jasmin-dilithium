#include <iostream>
#include <random>
#include <cstring>

extern "C" {
#include "../dilithium/ref/api.h"
#include "../dilithium/ref/params.h"
}

using std::cout;
using std::endl;
using std::vector;
using std::memcmp;

#define PRINT(X) cout << (#X) << " = " << (X) << endl

extern "C" {
	void keygen_jazz(uint8_t pk[pqcrystals_dilithium3_PUBLICKEYBYTES],
			uint8_t sk[pqcrystals_dilithium3_SECRETKEYBYTES],
			uint8_t randomness[SEEDBYTES]);
}

uint8_t sampleByte() {
	static std::random_device rd;
	static std::mt19937 gen(rd());
	static std::uniform_int_distribution<> distrib(0,  255);
	return distrib(gen);
}

int main() {
	uint8_t pk_ref[pqcrystals_dilithium3_PUBLICKEYBYTES];
	uint8_t sk_ref[pqcrystals_dilithium3_SECRETKEYBYTES];
	uint8_t pk_jazz[pqcrystals_dilithium3_PUBLICKEYBYTES];
	uint8_t sk_jazz[pqcrystals_dilithium3_SECRETKEYBYTES];

	uint8_t randomness[32] = { 0 };
	for(int i = 0; i < 32; ++i) {
		randomness[i] = sampleByte();
	}

	pqcrystals_dilithium3_ref_seeded_keypair(pk_ref, sk_ref, randomness);
	keygen_jazz(pk_jazz, sk_jazz, randomness);

	PRINT(memcmp(pk_ref, pk_jazz, pqcrystals_dilithium3_PUBLICKEYBYTES));
	PRINT(memcmp(sk_ref, sk_jazz, pqcrystals_dilithium3_SECRETKEYBYTES));

	for(int i = 0; i < pqcrystals_dilithium3_PUBLICKEYBYTES; ++i) {
		if(pk_ref[i] != pk_jazz[i]) {
			PRINT(i);
			break;
		}
	}

	for(int i = 96; i < pqcrystals_dilithium3_SECRETKEYBYTES; ++i) {
		if(sk_ref[i] != sk_jazz[i]) {
			PRINT(i);
			break;
		}
	}

	return 0;
}
