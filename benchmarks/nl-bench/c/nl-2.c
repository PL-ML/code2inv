int main() {
	int x;
	assume(x >= 0);
	int y = x * x;

	while(unknown()) {
		x = x + 1;
		y = y + 1;
	}

	assert(y <= x * x);
	return 0;
}


