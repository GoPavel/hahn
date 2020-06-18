import argparse
from collections import defaultdict
from typing import Optional
import attr
import re
import json

import matplotlib.pyplot as plt
import numpy as np

file_names = [
    'HahnRelationsBasic', 'HahnEquational',
    'HahnDom', 'HahnMaxElt', 'HahnMinElt',
    'HahnMinPath', 'HahnPath', 'HahnAcyclic',
    # 'HahnKat'
]

redefs = [
    'transitive', 'reflexive',
    'upward_closed', 'restr_rel',
    '[^w]max_elt', 'wmax_elt', '[^w]min_elt', 'wmin_elt',
    'DOM:', 'COD:', 'doma', 'domb',
]

# raw = defaultdict(list)

def def_occur(redef: str, s: str) -> bool:
    return bool(re.compile(f'{redef}').search(s))

def analyze(lemmas):
    prev, ans = '', True
    tactic_stat = {
        'kat': {'full': 0, 'partial': 0},
        'hkat': {'full': 0, 'partial': 0},
    }
    redef_stat = {d: {'full': 0, 'partial': 0, 'fail': 0} for d in redefs}
    for l in lemmas:
        is_full = None

        com = '' if l.comment is None else l.comment
        if 'Full' in com:
            is_full = 'full'
        elif 'Partial' in com:
            is_full = 'partial'
        else:
            for d in redefs:
                if def_occur(d, l.statement):
                    redef_stat[d]['fail'] += 1
            continue

        if "hkat'" in l.proof:
            tactic_stat['hkat'][is_full] += 1
        elif "kat'" in l.proof:
            tactic_stat['kat'][is_full] += 1
        else:
            raise ValueError(f'kat not in {l}')

        i = False
        for d in redefs:
            if def_occur(d, l.statement):
                i = True
                redef_stat[d][is_full] += 1
        # if not i and is_full == 'partial':
        #     print(l)

    total = {s: tactic_stat['kat'][s] + tactic_stat['hkat'][s] for s in ['full', 'partial']}

    redef_stat['other'] = { s: total[s] - sum(v[s] for k, v in redef_stat.items())
        for s in ['full', 'partial']
    }

    print(total)
    print('\n'.join(map(str, tactic_stat.items())))
    print('\n'.join(map(str, redef_stat.items())))

def draw():
    sizes = [proof_stat['total'] - (proof_stat['changed']), proof_stat['full'], proof_stat['partial']]
    print(f'proofs: {sizes}')
    # labels = f'Не именилось: {sizes[0]}', f'Упростилось: {sizes[1]}'
    explode = (0, 0.1, 0.1)

    plt.rcParams.update({'font.size': 28})
    plt.rcParams['figure.figsize'] = 16, 9

    fig, (ax1, ax2) = plt.subplots(1, 2)

    def func(pct, sizes):
        absolute = int(pct / 100. * sum(sizes))
        return "{:.1f}%\n({:d})".format(pct, absolute)

    ax1.pie(sizes, explode=explode, autopct=lambda pct: func(pct, sizes), startangle=90)
    ax1.set_title("Количество доказательств")
    ax1.axis('equal')  # Equal aspect ratio ensures that pie is drawn as a circle.
    ax1.legend(['Не изменилось', 'Полностью автоматизировано', 'Частично автоматизировано'])

    sizes = [2178, 320, 151]
    print(f'lines: {sizes}')
    # labels = (f'Не изменилось: {sizes[0]}', f'Упростилось: {sizes[1]}')
    ax2.pie(sizes, explode=(0, 0.1, 0.1), autopct=lambda pct: func(pct, sizes), startangle=90)
    ax2.set_title('Количество строк')
    ax2.axis('equal')
    plt.savefig('stat.png')


@attr.s(auto_attribs=True)
class Lemma:
    statement: str
    proof: str
    comment: Optional[str]
    name: str

    @classmethod
    def parse(cls, str):
        pass


def read_lemmas(path_dir):
    lemmas = []
    for name in file_names:
        path = f'{path_dir}/{name}.v'
        with open(path, 'r') as f:
            print(f'read {path}')
            lines = f.readlines()
        proof = []
        i = 0
        while i < (len(lines)):
            if "Lemma" in lines[i]:
                proof_lines = []
                statement_lines = []
                comment_line = lines[i-1]
                if not ('(*' in comment_line and '*)' in comment_line):
                    comment_line = None
                while True:
                    statement_lines.append(lines[i])
                    i += 1
                    if 'Proof' in lines[i]:
                        break
                while True:
                    proof_lines.append(lines[i])
                    if 'Qed' in lines[i]:
                        break
                    i += 1
                proof = ''.join(proof_lines)
                statement = ''.join(statement_lines)
                lemmas.append(Lemma(statement, proof, comment_line, name=statement_lines[0]))
            i += 1
    return lemmas


def main(args):
    new_lemmas = read_lemmas(args.new_dir)
    old_lemmas = read_lemmas(args.old_dir)

    if args.dump_changed:
        dump_changed(lemmas_new)
    elif args.calc_lines:
        with open(args.calc_lines, 'r') as f:
            data = json.load(f)
        new_cloc = {}
        old_cloc = {}
        for k, names in data.items():
            old_cloc[k] = calc_lines([l for l in old_lemmas if l.name in names])
            new_cloc[k] = calc_lines([l for l in new_lemmas if l.name in names])
        for k in sorted(data.keys()):
            print(f'{k}> -: {old_cloc[k]}, +: {new_cloc[k]}, d: {old_cloc[k] - new_cloc[k]}')
        cnt_same = 0
        for l1, l2 in zip([l for l in old_lemmas if l.name in data['all']],
                          [l for l in new_lemmas if l.name in data['all']]):
            if calc_lines([l1]) == calc_lines([l2]):
                cnt_same += 1
        print(f'proofs with same length: {cnt_same}')
    elif args.calc_redef:
        calc_redef(new_lemmas)
    else:
        analyze(new_lemmas)


def dump_changed(lemmas):
    data = defaultdict(list)
    for l in lemmas:
        if "kat'" in l.proof:
            data['all'].append(l.name)
        if "hkat'" in l.proof:
            data['hkat'].append(l.name)
        elif "kat'" in l.proof:
            data['kat'].append(l.name)
        for d in redefs:
            if def_occur(d, l.statement):
                data[d].append(l.name)
    with open('changed_lemmas.json', 'w') as f:
        json.dump(data, f)

def calc_lines(lemmas) -> int:
    total = 0
    for l in lemmas:
        total += len(l.proof.splitlines())
    return total


def calc_redef(lemmas):
    spec = 0
    proof = 0
    for l in lemmas:
        if l.comment is not None and 'redef_proof' in l.comment:
            spec += len(l.statement.splitlines())
            proof += len(l.proof.splitlines())

    print(f'spec: {spec}\nproof: {proof}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("new_dir", type=str)
    parser.add_argument("old_dir", type=str)
    parser.add_argument('--dump_changed', action='store_true')
    parser.add_argument('--calc_lines', type=str)
    parser.add_argument('--calc_redef', action='store_true')

    main(parser.parse_args())
