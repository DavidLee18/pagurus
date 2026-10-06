void *malloc(unsigned long);
void *calloc(unsigned long, unsigned long);
void *realloc(void *, unsigned long);
void free(void *);
void fm(void*a,void*b,void*c){free(b);}
int main(void){
    int*p=malloc(4);int*q=malloc(4);int*r=malloc(4);
    fm(p,q,r);free(p);free(r);return 0;
}
