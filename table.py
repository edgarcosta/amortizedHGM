import resource
import sys
from amortizedHGM import AmortizingHypergeometricData

def get_maxrss():
    # in mb
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024

def generate_row(cyclotomic_parameter, compare_parameter):
    H = AmortizingHypergeometricData(cyclotomic=cyclotomic_parameter)
    times = compare(H, **compare_parameter)
    if H.e == 1:
        times2 = compare(H, log2N=p['log2N'], t=p['t'], chained=False)
        for i, v in times2.items():
            for n, t in v.items():
                times[i][n] = t
    max_memory = get_maxrss()/1024.
    return ((c, H.e, H.degree(), H.weight(), H.alpha_beta()), times, max_memory)

def generate_row_latex(cyclotomic_parameter, compare_parameter, columns=11):
    row = generate_row(cyclotomic_parameter, compare_parameter)
    e = row[0][1]
    r = row[0][2]
    t = row[1]
    lines = []
    skip = len(t) - columns
    exponents = list(sorted(t))[skip:]
    lines.append(' & '.join([f"$e={e}, r={r}$"] + [f'$2^{{{i}}}$' for i in exponents]) + r"\\")
    lines.append(r'\hline')
    keys = {
        'Chained': r'\cite{costa-kedlaya-roe20}',
        'Amortized Gamma' : 'Phase (1)',
        'Additional precomputation': 'Phase (2)',
        'Amortized HG': 'Phase (3)',
        'Sage (p)' : r'\Sage ($p$)',
        'Magma (p)' : r'\Magma ($p$)',
        'Sage (q)' : r'\Sage ($q$)',
        'Magma (q)' : r'\Magma ($q$)',
    }
    for k, v in keys.items():
        line = [v]
        for i in exponents:
            if k in t[i]:
                n = t[i][k]
                if n < 10:
                    r = f'{n:.2f}'
                elif n < 100:
                    r = f'{n:.1f}'
                else:
                    r = f'{int(n)}'
                line.append(r)
        if len(line) > 1:
            lines.append(' & '.join(line) + r'\\')
        if k in ['Chained', 'Amortized HG', 'Magma (p)']:
            lines.append(r'\hline')
        if k == 'Magma (q)':
            if len(line) > 1:
                lines.append(r'\hline')
            lines.append(r'\\')
    return "\n".join(lines)


if __name__ == "__main__":
    cyclotomic_parameters = [
        [[4], [6]],
        [[10], [6, 6]],
        [[3, 4], [6,6]],
        [[2, 2, 5], [6, 6, 6]],
        [[2, 2, 3, 5], [6, 6, 6, 6]],
    ]
    compare_parameters = [
        {'log2N': 17, 't': 314/159, 'log2N_sage': 14, 'log2N_magma': 14},
        {'log2N': 27, 't': 314/159, 'log2N_sage': 17, 'log2N_magma': 17},
        {'log2N': 25, 't': 314/159, 'log2N_sage': 17, 'log2N_magma': 17,
        'log2N_higher_powers_sage': 23, 'log2N_higher_powers_magma': 21},
        {'log2N': 24, 't': 314/159, 'log2N_sage': 15, 'log2N_magma': 16,
        'log2N_higher_powers_sage': 23, 'log2N_higher_powers_magma': 21},
        {'log2N': 23, 't': 314/159, 'log2N_sage': 15, 'log2N_magma': 17,
        'log2N_higher_powers_sage': 24, 'log2N_higher_powers_magma': 22},
        {'log2N': 23, 't': 314/159, 'log2N_sage': 15, 'log2N_magma': 17,
        'log2N_higher_powers_sage': 21, 'log2N_higher_powers_magma': 20},
    ]
    for c, p in zip(cyclotomic_parameters, compare_parameters):
        print(f"% cyclotomic_parameters = {cyclotomic_parameters}")
        print(f"% compare_parameters = {compare_parameters}")
        print(generate_row_latex(c, p))
        print(f"% max memory {get_maxrss()}"}
        print("\n")
