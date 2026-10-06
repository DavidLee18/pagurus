/* FAIL: mutual recursion that frees the parameter is consuming. */
void *malloc(unsigned long n);
void free(void *p);

void b(int *q, int n);
void a(int *p, int n) {
    if (n)
        free(p);
    else
        b(p, 1);
}
void b(int *q, int n) { a(q, n); }

int main(int argc, char **argv) {
    int *p = malloc(4);
    a(p, argc);
    free(p);
    return 0;
}
