/* Inner `p` must not steal the outer owner's identity. */
void *malloc(unsigned long n);
void free(void *p);

int main(void) {
    void *p = malloc(8);
    {
        void *p = malloc(4);
        free(p);
    }
    free(p);
    return 0;
}
