void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void a(void*p){free(p);}
void b(void*p){a(p);}
int main(void){int*p=malloc(4);b(p);free(p);return 0;}
