int main() {
	int x, z, w;

	z = w * x;

	while(unknown())
	{
		w = w * x;
		z = z * x;
	}

	assert(z == w * x);
	return 0;
}
