/* FAIL: recursive free of the parameter is consuming. */
void *malloc(unsigned long n);
void free(void *p);

void w(int *p, int n) {
    if (n)
        free(p);
    else
        w(p, 1);
}

int main(int argc, char **argv) {
    int *p = malloc(4);
    w(p, argc);
    free(p);
    return 0;
}
