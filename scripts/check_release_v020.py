from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse,re,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[1]
C=ROOT/'certificates/v0.2.0'
GROUPS=[('HIST', 'TratadoAnalisis/Audit.lean', 'certificates/TA-LEAN-0010/AXIOMAS.txt', 833), ('API', 'tests/PublicAPI.lean', 'certificates/v0.1.2/API_AXIOMAS.txt', 25), ('P01', 'tests/Prerequisites.lean', 'certificates/v0.1.2/P01_AXIOMAS.txt', 22), ('P02', 'tests/AbsoluteValue.lean', 'certificates/v0.1.2/P02_AXIOMAS.txt', 21), ('P03', 'tests/CompletenessEquivalences.lean', 'certificates/v0.1.2/P03_AXIOMAS.txt', 29), ('P04', 'tests/NumeralArithmetic.lean', 'certificates/v0.1.2/P04_AXIOMAS.txt', 22), ('A1', 'tests/CauchyA1.lean', 'certificates/v0.2.0/A1_AXIOMAS.txt', 20), ('A2', 'tests/CauchyA2.lean', 'certificates/v0.2.0/A2_AXIOMAS.txt', 62), ('A3', 'tests/CauchyA3.lean', 'certificates/v0.2.0/A3_AXIOMAS.txt', 40), ('A4', 'tests/CauchyA4.lean', 'certificates/v0.2.0/A4_AXIOMAS.txt', 39), ('A5', 'tests/CauchyA5.lean', 'certificates/v0.2.0/A5_AXIOMAS.txt', 26), ('A6', 'tests/CauchyA6.lean', 'certificates/v0.2.0/A6_AXIOMAS.txt', 12), ('A7', 'tests/CauchyA7.lean', 'certificates/v0.2.0/A7_AXIOMAS.txt', 7), ('A8a', 'tests/CauchyA8a.lean', 'certificates/v0.2.0/A8a_AXIOMAS.txt', 37), ('A8b', 'tests/CauchyA8b.lean', 'certificates/v0.2.0/A8b_AXIOMAS.txt', 10), ('A8c', 'tests/CauchyA8c.lean', 'certificates/v0.2.0/A8c_AXIOMAS.txt', 11), ('A8d', 'tests/CauchyA8d.lean', 'certificates/v0.2.0/A8d_AXIOMAS.txt', 14)]
PINS={'certificates/TA-LEAN-0010/AXIOMAS.txt': 'ac6c676c2d9c3246123eb84e2da348b8c4df2bf43e059f4735bcafde865c5dc2', 'certificates/v0.1.2/API_AXIOMAS.txt': '363e29132154998981d4776d4cef5b6abcc9b92d92d1b410a8d9ab30427d90b9', 'certificates/v0.1.2/P01_AXIOMAS.txt': 'b3f0814b25f556c56252e15261509631a0a8da525775a52b30b5402d2b60d29e', 'certificates/v0.1.2/P02_AXIOMAS.txt': '5e5c6103ce9f439f82ee883443db6d141769403c0c74dc4296d9bfca4a039323', 'certificates/v0.1.2/P03_AXIOMAS.txt': 'afadd46a62fa6c1bd36ac014dc0bb21fdb934728a3045f3ebca1a9f09a36b4cf', 'certificates/v0.1.2/P04_AXIOMAS.txt': 'da4d657ee0672d2e8e0ca9a8980515f51889eec0c58e30959b1c68ebdb98fcf4', 'certificates/v0.2.0/A1_AXIOMAS.txt': '0ad47636734734d2ce6f40cab6143fe0f5474143d3aa56aaf13b85b5e837977f', 'certificates/v0.2.0/A1_QUERIES.txt': 'd3ccccb1f4c3b4064aa3f31e6de627303fe72e94e6864b12d0e65ee942349cc5', 'certificates/v0.2.0/A2_AXIOMAS.txt': '973f91473ec6713be203dc52ab5cd191bdccfdcb81c958ab18928902be55884c', 'certificates/v0.2.0/A2_QUERIES.txt': 'fd14e2ecc972f865f416a39aa23e2992a5b8db1724cb429e69fd2631f5c43adc', 'certificates/v0.2.0/A3_AXIOMAS.txt': '09c77f7395cebea0827c92fd1fb8d7b3cfa823cd19a0134f7c049f95ac04ebe6', 'certificates/v0.2.0/A3_QUERIES.txt': '2bde213bc68f65221033bae582f46fa7684402d654b6a7bab7db06a7df7b2057', 'certificates/v0.2.0/A4_AXIOMAS.txt': '805fb3e1e85248ed0be7f1201a5c2b8cba039f229abc15eed5bfe213d2209202', 'certificates/v0.2.0/A4_QUERIES.txt': 'c1aa07f65b51546bd610acfe0dfe51583eb24e04580e65d51781a88b235bd8ee', 'certificates/v0.2.0/A5_AXIOMAS.txt': '1c9d6d8ff89db2eb9766a8d86fbb45242b8fa47f00d236de7981d0390eca2eb7', 'certificates/v0.2.0/A5_QUERIES.txt': '96d22c1ac610d6f2c423d334d60cb4f0deb56ad01c6ff0ff7ad0998da3ba1c2a', 'certificates/v0.2.0/A6_AXIOMAS.txt': '1b4d7c83f29e646dbe59ea0e8654ce4fde9de1f581f373a96a3c768072ce5833', 'certificates/v0.2.0/A6_QUERIES.txt': 'ff8d263b66f749401c818e5f0186a974311c6b8283ad4f6fcd0bf65e5ed4a221', 'certificates/v0.2.0/A7_AXIOMAS.txt': '1f950f4cd63e77ce590117a7416fb77dda8298f809c049b944d75317e06620b6', 'certificates/v0.2.0/A7_QUERIES.txt': 'dcd8eceffef2a84bdbf0cacaa04a515ce06ab57159823d1db0ade082ee5bad6b', 'certificates/v0.2.0/A8a_AXIOMAS.txt': '37dc68e31a11a0146b296ede2057b15e3d34076859699d9276de82b4193b5b97', 'certificates/v0.2.0/A8a_QUERIES.txt': 'd8edae72c44a987e78f48c407803e127cc39f2f179d1bc2039693be5da023698', 'certificates/v0.2.0/A8b_AXIOMAS.txt': 'bbac85192ef37b5b56d0795dcae10f71593d06f336e5f97ab00027501d7c2346', 'certificates/v0.2.0/A8b_QUERIES.txt': '89d8ac8fdd9352c69d39c31f1f03de324c58e01d6a6d7047b07a05085f622dd8', 'certificates/v0.2.0/A8c_AXIOMAS.txt': 'f8f5a2b8b1d80b24f4b4b238be2dd078a36ccf3093c72c6918570e4980391735', 'certificates/v0.2.0/A8c_QUERIES.txt': 'ac4a9d72b441879bec67c81a8f7736118fe83817371147a4dd54091786ccf578', 'certificates/v0.2.0/A8d_AXIOMAS.txt': '37eaadf5701005dd6e3493090c629cc34719d81856f9c79b7f670a6b71410ecb', 'certificates/v0.2.0/A8d_QUERIES.txt': '816a3b7849e73d51f22c3f07881f2975b3770d3e8b87f99ba9d987f6decac93e', 'certificates/TA-LEAN-0010/SHA256SUMS': '70c86f483ba75671dc695f5ae834d255e94aee357ff7932736885f188007fea6', 'certificates/v0.1.1/SHA256SUMS': 'b2acf1ca4b0a31ae05284e55508f0204f07c663138e76644328bca11decf4282', 'certificates/v0.1.2/SHA256SUMS': 'b94479ffa0f7c35b5b0877167ea64a4c2178dfc1c2034d72499475998330bf91', 'certificates/v0.1.2/AXIOMAS.txt': '603b2708f0707c4de16d2aad4689b6c25ef889b5739d211b179ca8e932157acf', 'certificates/v0.2.0/SHA256SUMS': '59ad422c533a6e420e5f60f852689c23bb6d42c62a237bf385c870d01d23b845', 'certificates/v0.2.0/AXIOMAS.txt': 'd2c082787a1e3c1f10323d79d75ed874230990bb3762b71ea750338e3180d3ef', 'certificates/v0.2.0/IMPORTS-LOCALES.txt': '549dcad050bac3b473d2708af7c3224839e2f4f30a091b8a6900772477f4a35d'}
STRICT=['TratadoAnalisis/Cauchy/Bisection.lean', 'TratadoAnalisis/Cauchy/BisectionInvariants.lean', 'TratadoAnalisis/Cauchy/BisectionWidths.lean', 'TratadoAnalisis/Cauchy/BoundedSequences.lean', 'TratadoAnalisis/Cauchy/CauchySequences.lean', 'TratadoAnalisis/Cauchy/ConvergentIsCauchy.lean', 'TratadoAnalisis/Cauchy/RationalConvergence.lean', 'TratadoAnalisis/Cauchy/SequentialIncompleteness.lean']
CONFIG={'lean-toolchain','lakefile.toml','lake-manifest.json'}
def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def digest(p):return sha256(p.read_bytes()).hexdigest()
def manifest(p):
 d={}
 for l in p.read_text(encoding='utf-8-sig').splitlines():
  h,n=l.split('  ',1);need(n not in d and re.fullmatch('[0-9a-fA-F]{64}',h) and not Path(n).is_absolute() and '..' not in Path(n).parts,'Invalid manifest');d[n]=h.lower()
 return d
def baseline(p):
 d={}
 for l in p.read_text(encoding='utf-8-sig').splitlines():
  n,a=l.split('|',1);need(n not in d,'Duplicate baseline');d[n]=() if a=='<none>' else tuple(sorted(a.split(',')))
 return d
def logs(p):
 d={}
 for n,a in re.findall(r"(?m)^'([^'\r\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on (?:any )?axioms)[ \t]*\r?$",p.read_text(encoding='utf-8-sig')):
  need(n not in d,'Duplicate audit output: '+n);d[n]=tuple(sorted(x.strip() for x in a.split(',') if x.strip()))
 return d
def static():
 for n,h in PINS.items():need(digest(ROOT/n)==h,'Certificate changed: '+n)
 m=manifest(C/'SHA256SUMS');old=manifest(ROOT/'certificates/v0.1.2/SHA256SUMS');need(len(m)==185 and len(old)==159 and all(m.get(n)==h for n,h in old.items()),'Historical source regression')
 tracked=subprocess.check_output(['git','ls-files','-z'],cwd=ROOT).decode('utf-8').split('\0');need({n for n in tracked if n.endswith('.lean') or n in CONFIG}==set(m),'Source inventory mismatch')
 for n,h in m.items():need(digest(ROOT/n)==h,'Source changed: '+n)
 pending=['TratadoAnalisis.Foundations.FunctionSpace','TratadoAnalisis.Foundations.RelationalFunctions','TratadoAnalisis.Rationals.AbsoluteValue']+[n[:-5].replace('/','.') for n in m if n.startswith('TratadoAnalisis/Cauchy/') and n.endswith('.lean')];seen=set()
 while pending:
  n=pending.pop()
  if n in seen:continue
  need(n!='TratadoAnalisis' and not n.startswith(('TratadoAnalisis.Dedekind','TratadoAnalisis.Abstract','TratadoAnalisis.Bridges','TratadoAnalisis.Chapter7_0010')),'Forbidden import: '+n);seen.add(n)
  pending.extend(x for x in re.findall(r'(?m)^\s*(?:public\s+)?import\s+(\S+)',(ROOT/(n.replace('.','/')+'.lean')).read_text(encoding='utf-8-sig')) if x.startswith('TratadoAnalisis'))
 need(len(seen)==52 and seen==set((C/'IMPORTS-LOCALES.txt').read_text().splitlines()),'Import closure mismatch');print('PASS: 185/185 sources; 159/159 historical; 52 independent modules',flush=True)
def audit(logdir):
 merged={}
 for k,probe,ref,n in GROUPS:
  b=baseline(ROOT/ref);g=logs(logdir/(k+'.log'));need(len(b)==n and g==b and not set(g)&set(merged),'Audit mismatch: '+k);merged.update(g);print(f'PASS {k}: {n} exact fingerprints',flush=True)
 need(len(merged)==1230 and merged==baseline(C/'AXIOMAS.txt'),'Aggregate mismatch');need(Counter(merged.values())==Counter({('Quot.sound','propext'):1150,('Classical.choice','Quot.sound','propext'):65,('Quot.sound',):6,('propext',):4,():5}),'Axiom distribution mismatch');print('PASS-RELEASE-CANDIDATE-v0.2.0: 1230/1230; 65 historical Choice; zero new Choice; zero sorryAx',flush=True)
def run(args,path):
 p=subprocess.run(['lake','env','lean',*args],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);path.write_bytes(p.stdout)
 if p.returncode:print(p.stdout.decode('utf-8',errors='replace')[-16000:],flush=True);raise RuntimeError('Lean failed: '+str(args))
def main():
 a=argparse.ArgumentParser();a.add_argument('--static',action='store_true');a.add_argument('--logs',type=Path);a=a.parse_args();static()
 if a.static:return
 if a.logs:audit(a.logs);return
 with tempfile.TemporaryDirectory(prefix='ta-c08-ci-') as td:
  t=Path(td)
  for n in STRICT:print('Strict: '+n,flush=True);run(['-DwarningAsError=true',n],t/(Path(n).stem+'-strict.log'))
  for k,probe,ref,n in GROUPS:print('Kernel audit: '+k,flush=True);run([probe],t/(k+'.log'))
  audit(t)
 static()
if __name__=='__main__':main()
