int main() {
	int x, y, z, w;

	assume(x == 1 && x <= y);
	w = 1;
	z = 1;

	while(x <= y)
	{
		w = w * x;
		if (x < y) {
			z = z * x;
		}
		x += 1;
	}

	assert(w == z * y);
	return 0;
}
