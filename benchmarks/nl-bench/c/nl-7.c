int main() {
	int x, y, z, w;

	assume(x >= 0 && y >= x);

	z = 0;
	w = 0;

	while(w < y) {
		z += x;
		w += 1;
	}

	assert(z == x * y);

	return 0;
}
