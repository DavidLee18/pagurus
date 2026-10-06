void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void c2(void*a,void*b){free(a);free(b);}
int main(void){int*p=malloc(4);c2(p,p);return 0;}
