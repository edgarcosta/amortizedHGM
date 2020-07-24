from sage.rings.rational_field import QQ
import array

cdef long mbound_c_ints(long p, int start_num, int start_den, int end_num, int end_den):
    return max((end_num * (p-1)) // end_den - (start_num * (p-1)) // start_den, 1)

cpdef mbound_dict_c(indices, start, end):
    cdef int i, n, start_num, start_den, end_num, end_den
    start = QQ(start)
    end = QQ(end)
    start_num = start.numer()
    start_den = start.denom()
    end_num = end.numer()
    end_den = end.denom()
    n = len(indices)
    l = array.array('l', [0]) * n
    for i in range(n):
        l[i] = mbound_c_ints(indices[i], start_num, start_den, end_num, end_den)
    return dict(zip(indices, l))
