#include <iostream>
#include <random>
#include <cstring>
#include <string>
#include <stdexcept>
#include <array>

extern "C" {
#include "../dilithium/ref/api.h"
#include "../dilithium/ref/params.h"
#include "../dilithium/ref/poly.h"
#include "../dilithium/ref/polyvec.h"
#include "../dilithium/ref/packing.h"
}

using std::cout;
using std::endl;
using std::vector;
using std::memcmp;
using std::runtime_error;
using std::to_string;
using std::array;

#define PRINT(X) cout << (#X) << " = " << (X) << endl

extern "C" {
	void pack_t1_jazz(uint32_t p[N], uint8_t buf[POLYT1_PACKEDBYTES]);
	void polyt1_unpack_jazz(uint8_t buf[POLYT1_PACKEDBYTES], int32_t t1[N]);
	void polyz_unpack_jazz(int32_t p[N], uint8_t buf[POLYZ_PACKEDBYTES]);
	void polyz_pack_jazz(uint8_t buf[POLYZ_PACKEDBYTES], int32_t p[N]);
	void polyeta_unpack_jazz(int32_t p[N], uint8_t buf[POLYETA_PACKEDBYTES]);
	void polyt0_unpack_jazz(int32_t p[N], uint8_t buf[POLYETA_PACKEDBYTES]);
	void pack_signature_jazz(uint8_t c_tilde[32],
			int32_t z[L * N], int32_t h[K * N], uint8_t sig[CRYPTO_BYTES]);
}

uint8_t sampleByte() {
	static std::random_device rd;
	static std::mt19937 gen(rd());
	static std::uniform_int_distribution<> distrib(0,  255);
	return distrib(gen);
}

uint32_t sample_t1_component() {
	static std::random_device rd;
	static std::mt19937 gen(rd());
	static std::uniform_int_distribution<> distrib(0,  1023);
	return distrib(gen);
}

uint32_t sample_z_component() {
	static std::random_device rd;
	static std::mt19937 gen(rd());
	static std::uniform_int_distribution<> distrib(0,  (1 << 20) - 1);
	return distrib(gen);
}

void test_pack_t1() {
	poly p;
	uint32_t uint_p[N];
	for(int i = 0; i < N; ++i) {
		uint32_t val = sample_t1_component(); 
		p.coeffs[i] = val;
		uint_p[i] = val;
	}

	uint8_t buf_ref[POLYT1_PACKEDBYTES];

	pqcrystals_dilithium3_ref_polyt1_pack(buf_ref, &p);

	uint8_t buf_jazz[POLYT1_PACKEDBYTES];
	pack_t1_jazz(uint_p, buf_jazz);

	if(memcmp(buf_ref, buf_jazz, POLYT1_PACKEDBYTES) != 0) {
		throw runtime_error("test failed at " + to_string(__LINE__));
	}
}

void test_unpack_t1() {
	poly p;
	for(int i = 0; i < N; ++i) {
		int32_t val = sample_t1_component(); 
		p.coeffs[i] = val;
	}

	uint8_t buf[POLYT1_PACKEDBYTES];
	pqcrystals_dilithium3_ref_polyt1_pack(buf, &p);

	int32_t p_jazz[N];

	polyt1_unpack_jazz(buf, p_jazz);

	for(int i = 0; i < N; ++i) {
		if(p_jazz[i] != p.coeffs[i]) {
			PRINT(i);
			PRINT(p_jazz[i]);
			PRINT(p.coeffs[i]);
			throw runtime_error("test failed at " + to_string(__LINE__));
		}
	}
}

void test_pack_z() {
	poly p;

	for(int i = 0; i < N; ++i)
		p.coeffs[i] = sample_z_component();

	uint8_t buf_ref[POLYZ_PACKEDBYTES];
	pqcrystals_dilithium3_ref_polyz_pack(buf_ref, &p);

	uint8_t buf_jazz[POLYZ_PACKEDBYTES];
	polyz_pack_jazz(buf_jazz, p.coeffs);

	for(int i = 0; i < POLYZ_PACKEDBYTES; ++i) {
		if(buf_ref[i] != buf_jazz[i]) {
			PRINT(i);
			PRINT(int(buf_ref[i]));
			PRINT(int(buf_jazz[i]));
			throw runtime_error("test failed at " + to_string(__LINE__));
		}
	}
}

void test_unpack_z() {
	poly p_ref;
	int32_t p_jazz[N];
	
	uint8_t buf[POLYZ_PACKEDBYTES];
	for(int i = 0; i < POLYZ_PACKEDBYTES; ++i) {
		buf[i] = sampleByte();
	}

	polyz_unpack(&p_ref, buf); 
	polyz_unpack_jazz(p_jazz, buf);


	for(int i = 0; i < N; ++i) {
		if(p_ref.coeffs[i] != p_jazz[i]) {
			PRINT(i);
			PRINT(p_ref.coeffs[i]);
			PRINT(p_jazz[i]);
			throw runtime_error("test failed at " + to_string(__LINE__));
		}
	}
}

void test_unpack_eta() {
	poly p_ref;
	int32_t p_jazz[N];
	
	uint8_t buf[POLYETA_PACKEDBYTES];
	for(int i = 0; i < POLYETA_PACKEDBYTES; ++i) {
		buf[i] = sampleByte();
	}

	polyeta_unpack(&p_ref, buf); 
	polyeta_unpack_jazz(p_jazz, buf);

	for(int i = 0; i < N; ++i) {
		if(p_ref.coeffs[i] != p_jazz[i]) {
			PRINT(i);
			PRINT(p_ref.coeffs[i]);
			PRINT(p_jazz[i]);
			throw runtime_error("test failed at " + to_string(__LINE__));
		}
	}
}

void test_unpack_t0() {
	poly p_ref;
	int32_t p_jazz[N];
	
	uint8_t buf[POLYT0_PACKEDBYTES];
	for(int i = 0; i < POLYT0_PACKEDBYTES; ++i) {
		buf[i] = sampleByte();
	}

	polyt0_unpack(&p_ref, buf); 
	polyt0_unpack_jazz(p_jazz, buf);

	for(int i = 0; i < N; ++i) {
		if(p_ref.coeffs[i] != p_jazz[i]) {
			PRINT(i);
			PRINT(p_ref.coeffs[i]);
			PRINT(p_jazz[i]);
			throw runtime_error("test failed at " + to_string(__LINE__));
		}
	}
}

array<int32_t, K * N> sample_h() {
	static std::random_device rd;
	static std::mt19937 gen(rd());
	static std::uniform_int_distribution<> distrib(0,  K * N - 1);
	array<int32_t, K * N> arr = {};
	for(int i = 0; i < 40; ++i) {
		int loc = distrib(gen);
		arr[loc] = 1;
	}
	return arr;
}

void test_pack_signature() {
	uint8_t c_tilde[32];
	for(int i = 0; i < 32; ++i) {
		c_tilde[i] = sampleByte();
	}

	//zero-init?
	int32_t z_jazz[L * N];
	polyvecl z_ref;

	for(int i = 0; i < L; ++i) {
		for(int j = 0; j < N; ++j) {
			auto z_comp = sample_z_component();
			z_jazz[i * N + j] = z_comp;
			z_ref.vec[i].coeffs[j] = z_comp;
		}
	}

	auto h = sample_h();

	uint8_t sig_jazz[CRYPTO_BYTES];
	pack_signature_jazz(c_tilde, z_jazz, h.data(), sig_jazz);

	uint8_t sig_ref[CRYPTO_BYTES];
	polyveck h_ref;
	for(int i = 0; i < K; ++i) {
		for(int j = 0; j < N; ++j) {
			h_ref.vec[i].coeffs[j] = h[i * N + j];
		}
	}
	pack_sig(sig_ref, c_tilde, &z_ref, &h_ref);

	for(int i = 0; i < CRYPTO_BYTES; ++i) {
		if(sig_ref[i] != sig_jazz[i]) {
			PRINT(i);
			PRINT(int(sig_ref[i]));
			PRINT(int(sig_jazz[i]));
			throw runtime_error("test failed at " + to_string(__LINE__));
		}
	}
}


int main() {
	test_pack_t1();
	test_unpack_t1();
	test_unpack_z();
	test_unpack_eta();
	test_unpack_t0();
	test_pack_z();
	test_pack_signature();
	return 0;
}
