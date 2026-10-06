void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void sink(int*p){free(p);}
int main(void){int*p=malloc(4);sink(p);free(p);return 0;}
