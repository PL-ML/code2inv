int main() {
	int x;
	int y;

	assume(x >= 0 && y >= 0);

	int z = x * y;

	while(x > 0) {
		x = x - 1;
		z = z - y;
	}

	assert(z == 0);
	return 0;
}
