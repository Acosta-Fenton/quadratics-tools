/* Shared engine for the quadratic solving tools.
   Each tool page sets window.TOOL to "factoring", "quadformula" or "sqrt".
   Generated problems never have complex answers. */
(function(){
'use strict';

var TOOL = window.TOOL;

/* ================= exact fractions ================= */
function gcd(a,b){ a=Math.abs(a); b=Math.abs(b); while(b){ var t=a%b; a=b; b=t; } return a; }
function F(n,d){ if(d===undefined) d=1; if(d<0){ n=-n; d=-d; } var g=gcd(n,d)||1; return {n:n/g, d:d/g}; }
function add(x,y){ return F(x.n*y.d+y.n*x.d, x.d*y.d); }
function sub(x,y){ return F(x.n*y.d-y.n*x.d, x.d*y.d); }
function mul(x,y){ return F(x.n*y.n, x.d*y.d); }
function div(x,y){ return F(x.n*y.d, x.d*y.n); }
function neg(x){ return F(-x.n, x.d); }
function abs(x){ return F(Math.abs(x.n), x.d); }
function sq(x){ return mul(x,x); }
function num(x){ return x.n/x.d; }
function sgn(x){ return x.n>0 ? 1 : (x.n<0 ? -1 : 0); }
function isInt(x){ return x.d===1; }
function eq(x,y){ return x.n===y.n && x.d===y.d; }
function nonzero(x){ return x.n!==0; }
function sqrtFrac(s){
  if(s.n<0) return null;
  var rn=Math.round(Math.sqrt(s.n)), rd=Math.round(Math.sqrt(s.d));
  return (rn*rn===s.n && rd*rd===s.d) ? F(rn,rd) : null;
}
function simpRad(n){
  var s=1, t=n;
  for(var f=2; f*f<=t; f++){ while(t%(f*f)===0){ t/=f*f; s*=f; } }
  return {s:s, t:t};
}

/* ================= number formatting ================= */
var MINUS='\u2212';
function fmt(x){
  var s=x.n<0 ? MINUS : '', an=Math.abs(x.n);
  return x.d===1 ? s+an : s+an+'/'+x.d;
}
function fmtN(v){
  return (v<-0.004 ? MINUS : '')+Math.abs(v).toFixed(2);
}
function termDec(x){
  var dd=x.d, t=0, f=0;
  while(dd%2===0){ dd/=2; t++; }
  while(dd%5===0){ dd/=5; f++; }
  return dd===1 ? (x.n<0 ? MINUS : '')+(Math.abs(x.n)/x.d).toFixed(Math.max(t,f)) : null;
}
function ansNum(x){
  if(isInt(x)) return fmt(x);
  var td=termDec(x);
  return fmt(x)+' <small>('+(td ? '= '+td : '\u2248 '+fmtN(num(x)))+')</small>';
}
function par(x){ return '('+fmt(x)+')'; }
function parNeg(x){ return x.n<0 ? '('+fmt(x)+')' : fmt(x); }
function listJoin(a){
  if(a.length<=1) return a.join('');
  if(a.length===2) return a[0]+' and '+a[1];
  return a.slice(0,-1).join(', ')+', and '+a[a.length-1];
}

/* ================= expression helpers ================= */
var X='<i>x</i>';
function T(h){ return {t:h}; }
function M(h){ return {m:h}; }
function polyHTML(items){
  var out='';
  items.forEach(function(it){
    var c=it[0], body=it[1];
    if(c.n===0) return;
    var mag=abs(c);
    var text = body ? (eq(mag,F(1)) ? body : fmt(mag)+body) : fmt(mag);
    if(!out) out=(c.n<0 ? MINUS : '')+text;
    else out += (c.n<0 ? ' '+MINUS+' ' : ' + ')+text;
  });
  return out || '0';
}
function coefStr(a){ return eq(abs(a),F(1)) ? (a.n<0 ? MINUS : '') : fmt(a); }
function sg(m){ return m.n>=0 ? ' + '+fmt(m) : ' '+MINUS+' '+fmt(abs(m)); }
function varsOf(i){ return i===0 ? X+'\u00b2' : (i===1 ? X : ''); }
function sideItems(c){ return [[c[0],varsOf(0)],[c[1],varsOf(1)],[c[2],'']]; }
function polySide(c){ return polyHTML(sideItems(c)); }
function stdEqHTML(A,B,C){ return polySide([A,B,C])+' = 0'; }
function termText(mag,v){ return (v && eq(mag,F(1))) ? v : fmt(mag)+v; }
function cap(s){ return s.charAt(0).toUpperCase()+s.slice(1); }

function sqrtExprInner(hs){ return hs.n===0 ? X : X+(hs.n>0 ? ' + ' : ' '+MINUS+' ')+fmt(abs(hs)); }
function sqSquared(hs){ return hs.n===0 ? X+'\u00b2' : '('+sqrtExprInner(hs)+')\u00b2'; }
function sqSide(a,hs,c){
  var out=coefStr(a)+sqSquared(hs);
  if(c.n!==0) out += (c.n>0 ? ' + ' : ' '+MINUS+' ')+fmt(abs(c));
  return out;
}

/* ================= equation models =================
   poly:   L, R are [x\u00b2, x, 1] coefficient triples (fractions)
   prod:   (x + m)(x + n) = rhs
   xprod:  x(x + b) = rhs
   sqrt:   a(x + hs)\u00b2 + c = e(x + hs)\u00b2 + d                              */
function eqText(E){
  if(E.kind==='prod') return '('+X+sg(E.m)+')('+X+sg(E.n)+') = '+fmt(E.rhs);
  if(E.kind==='xprod') return X+'('+X+sg(E.b)+') = '+fmt(E.rhs);
  if(E.kind==='sqrt') return sqSide(E.a,E.hs,E.c)+' = '+(nonzero(E.e) ? sqSide(E.e,E.hs,E.d) : fmt(E.d));
  return polySide(E.L)+' = '+polySide(E.R);
}
function evalSide(E,which,x){
  var xs=fmt(x), px='('+xs+')';
  if(E.kind==='poly'){
    var c=E[which];
    return {sub:polyHTML([[c[0],px+'\u00b2'],[c[1],px],[c[2],'']]),
            val:add(add(mul(c[0],sq(x)),mul(c[1],x)),c[2])};
  }
  if(E.kind==='prod'){
    if(which==='R') return {sub:fmt(E.rhs), val:E.rhs};
    var f=function(m){ return '('+xs+(m.n>=0 ? ' + ' : ' '+MINUS+' ')+fmt(abs(m))+')'; };
    return {sub:f(E.m)+f(E.n), val:mul(add(x,E.m),add(x,E.n))};
  }
  if(E.kind==='xprod'){
    if(which==='R') return {sub:fmt(E.rhs), val:E.rhs};
    return {sub:px+'('+xs+(E.b.n>=0 ? ' + ' : ' '+MINUS+' ')+fmt(abs(E.b))+')', val:mul(x,add(x,E.b))};
  }
  var u2='('+xs+(E.hs.n===0 ? '' : (E.hs.n>0 ? ' + ' : ' '+MINUS+' ')+fmt(abs(E.hs)))+')\u00b2';
  var sqv=sq(add(x,E.hs));
  if(which==='L') return {sub:polyHTML([[E.a,u2],[E.c,'']]), val:add(mul(E.a,sqv),E.c)};
  return {sub:polyHTML([[E.e,u2],[E.d,'']]), val:add(mul(E.e,sqv),E.d)};
}
function evalNum(E,x){
  function side(k){
    if(E.kind==='poly'){ var c=E[k]; return num(c[0])*x*x+num(c[1])*x+num(c[2]); }
    if(E.kind==='prod') return k==='L' ? (x+num(E.m))*(x+num(E.n)) : num(E.rhs);
    if(E.kind==='xprod') return k==='L' ? x*(x+num(E.b)) : num(E.rhs);
    var u=x+num(E.hs);
    return k==='L' ? num(E.a)*u*u+num(E.c) : num(E.e)*u*u+num(E.d);
  }
  return side('L')-side('R');
}

/* ================= get to standard form ================= */
function standardize(E, flip){
  var steps=[], L=E.L, R=E.R, lines, i;
  if(E.kind==='prod' || E.kind==='xprod'){
    lines=[];
    if(E.kind==='prod'){
      var m=E.m, n=E.n, mn=mul(m,n);
      lines.push(T('Multiply out the left side. Multiply each term in the first parentheses by each term in the second (FOIL):'));
      lines.push(M('('+X+sg(m)+')('+X+sg(n)+') = '+polyHTML([[F(1),X+'\u00b2'],[n,X],[m,X],[mn,'']])));
      lines.push(T('Combine like terms:'));
      L=[F(1),add(m,n),mn];
    } else {
      lines.push(T('Distribute '+X+' to each term inside the parentheses:'));
      L=[F(1),E.b,F(0)];
    }
    R=[F(0),F(0),E.rhs];
    lines.push(M(polySide(L)+' = '+fmt(E.rhs)));
    steps.push({title:'Multiply out the parentheses', lines:lines});
  }
  var A=sub(L[0],R[0]), B=sub(L[1],R[1]), C=sub(L[2],R[2]);
  var needMove=R.some(nonzero);
  if(needMove){
    var ops=[];
    for(i=0;i<3;i++) if(nonzero(R[i])) ops.push((sgn(R[i])>0 ? 'subtract ' : 'add ')+termText(abs(R[i]),varsOf(i)));
    lines=[];
    if(ops.length===1){
      var o=ops[0];
      lines.push(T(cap(o)+(o.indexOf('subtract')===0 ? ' from' : ' to')+' both sides so the right side becomes 0:'));
    } else {
      lines.push(T('Do the opposite operation on both sides for every term on the right: '+listJoin(ops)+'. The right side becomes 0:'));
    }
    var both=false;
    for(i=0;i<3;i++) if(nonzero(L[i]) && nonzero(R[i])) both=true;
    if(both){
      var items=[];
      for(i=0;i<3;i++){ items.push([L[i],varsOf(i)]); items.push([neg(R[i]),varsOf(i)]); }
      lines.push(M(polyHTML(items)+' = 0'));
      lines.push(T('Combine like terms:'));
    }
    lines.push(M(stdEqHTML(A,B,C)));
    steps.push({title:'Get 0 on one side', lines:lines});
  }
  if(flip && sgn(A)<0){
    A=neg(A); B=neg(B); C=neg(C);
    steps.push({title:'Make the '+X+'\u00b2 term positive', lines:[
      T('The '+X+'\u00b2 term is negative. Divide both sides by '+MINUS+'1 (this flips every sign):'),
      M(stdEqHTML(A,B,C))
    ]});
  }
  return {steps:steps, A:A, B:B, C:C};
}

function notQuadratic(res, S){
  res.steps.push({title:'Check the equation', gives:true, lines:[
    T('After moving the terms, the '+X+'\u00b2 terms cancel. This is a linear equation, not a quadratic, so this tool does not apply.')
  ]});
  res.answer='Not a quadratic equation';
  res.solNums=[];
  return res;
}

function checkStep(E, sols){
  var lines=[];
  sols.forEach(function(r){
    var l=evalSide(E,'L',r), rr=evalSide(E,'R',r);
    lines.push(T('Try '+X+' = '+fmt(r)+':'));
    lines.push(M('Left side: '+l.sub+' = '+fmt(l.val)));
    lines.push(M('Right side: '+(rr.sub===fmt(rr.val) ? rr.sub : rr.sub+' = '+fmt(rr.val))+'   \u2713'));
  });
  lines.push(T('Both sides match for each answer, so the solutions check out.'));
  return {title:'Check your answers', lines:lines};
}
function ansText(sols){
  if(sols.length===1) return X+' = '+ansNum(sols[0])+' <small>(only one solution)</small>';
  return sols.map(function(r){ return X+' = '+ansNum(r); }).join('  or  ');
}
function sortF(a){ return a.slice().sort(function(u,v){ return num(u)-num(v); }); }

/* ================= factoring ================= */
function findFactors(a,b,c){
  var ac=Math.abs(c);
  for(var p=1;p<=a;p++){
    if(a%p) continue;
    var r=a/p;
    for(var d=1;d<=ac;d++){
      if(ac%d) continue;
      for(var sgn2=-1;sgn2<=1;sgn2+=2){
        var q=sgn2*d, s=c/q;
        if(p*s+q*r===b) return {p:p,q:q,r:r,s:s};
      }
    }
  }
  return null;
}
function facHTML(p,q){
  var co = p===1 ? '' : p;
  if(q===0) return co+X;
  return '('+co+X+(q<0 ? ' '+MINUS+' ' : ' + ')+Math.abs(q)+')';
}
function pairsText(n){
  var out=[]; for(var i=1;i*i<=n;i++){ if(n%i===0) out.push(i+' \u00d7 '+(n/i)); } return out.join(', ');
}
function buildFactoring(E){
  var S=standardize(E,true);
  var res={eqHTML:eqText(E), steps:S.steps.slice(), answer:'', solNums:[], E:E};
  if(S.A.n===0) return notQuadratic(res,S);
  var a=S.A.n, b=S.B.n, c=S.C.n;
  var g=gcd(gcd(a,Math.abs(b)),Math.abs(c));
  if(g>1){
    a/=g; b/=g; c/=g;
    res.steps.push({title:'Divide out the common factor', lines:[
      T('Every term is divisible by '+g+'. Divide both sides by '+g+' (0 \u00f7 '+g+' is still 0):'),
      M(stdEqHTML(F(a),F(b),F(c)))
    ]});
  }
  var std=stdEqHTML(F(a),F(b),F(c));
  var D=b*b-4*a*c, fl, i;
  if(c===0){
    fl=[{p:1,q:0},{p:a,q:b}];
    res.steps.push({title:'Factor', lines:[
      T('There is no constant term, so every term has an '+X+'. Factor out the common factor '+X+':'),
      M(b===0 ? X+' \u00b7 '+X+' = 0' : X+facHTML(a,b)+' = 0')
    ]});
  } else {
    var sr=D>=0 ? Math.round(Math.sqrt(D)) : -1;
    if(D<0){
      res.steps.push({title:'Try to factor', gives:true, lines:[
        T('Look for factors of '+std.replace(' = 0','')+'. No real numbers make it work, so this trinomial can\u2019t be factored.'),
        T('This equation has <b>no real solutions</b>. (Its graph never touches the '+X+'-axis.)')
      ]});
      res.answer='No real solutions';
      return res;
    }
    if(sr*sr!==D){
      res.steps.push({title:'Try to factor', gives:true, lines:[
        T('Look for two whole-number factors of '+std.replace(' = 0','')+'. No pair of whole numbers works, so it does not factor with whole numbers.'),
        T('Use another method for this one, like the quadratic formula.')
      ]});
      res.answer='Does not factor with whole numbers. Try the quadratic formula.';
      return res;
    }
    var f=findFactors(a,b,c);
    fl=[{p:f.p,q:f.q},{p:f.r,q:f.s}];
    var lines=[];
    if(a===1){
      lines.push(T('Find two numbers that multiply to '+fmt(F(c))+' and add to '+fmt(F(b))+'. Those numbers are '+fmt(F(f.q))+' and '+fmt(F(f.s))+'.'));
    } else {
      lines.push(T('Factor the trinomial using guess and check. The '+X+'-coefficients must multiply to '+a+' ('+pairsText(a)+'), and the constants must multiply to '+fmt(F(c))+' (factor pairs of '+Math.abs(c)+': '+pairsText(Math.abs(c))+'). Try pairs until the middle term works.'));
    }
    lines.push(M(facHTML(f.p,f.q)+facHTML(f.r,f.s)+' = 0'));
    if(a>1){
      lines.push(T('Check the middle term by multiplying:'));
      lines.push(M(facHTML(f.p,f.q)+facHTML(f.r,f.s)+' = '+polyHTML([[F(f.p*f.r),X+'\u00b2'],[F(f.p*f.s),X],[F(f.q*f.r),X],[F(f.q*f.s),'']])+' = '+polyHTML([[F(a),X+'\u00b2'],[F(b),X],[F(c),'']])+'   \u2713'));
    }
    res.steps.push({title:'Factor', lines:lines});
  }
  // zero product
  var zl=[T('Zero product property: if two things multiply to give 0, at least one of them must be 0. Set each factor equal to 0 and solve:')];
  var roots=[];
  fl.forEach(function(fc){
    var root=F(-fc.q,fc.p); roots.push(root);
    if(fc.q===0 && fc.p===1) zl.push(M(X+' = 0'));
    else if(fc.p===1) zl.push(M(X+(fc.q>0 ? ' + ' : ' '+MINUS+' ')+Math.abs(fc.q)+' = 0   \u2192   '+X+' = '+fmt(root)));
    else {
      zl.push(M(fc.p+X+(fc.q>=0 ? ' + ' : ' '+MINUS+' ')+Math.abs(fc.q)+' = 0'));
      zl.push(M(fc.p+X+' = '+fmt(F(-fc.q))));
      zl.push(M(X+' = '+fmt(root)));
    }
  });
  var uniq=sortF(roots);
  if(uniq.length===2 && eq(uniq[0],uniq[1])){ uniq=[uniq[0]]; zl.push(T('Both factors give the same answer, so there is only one solution.')); }
  res.steps.push({title:'Use the zero product property', gives:true, lines:zl});
  res.solNums=uniq.map(num);
  res.answer=ansText(uniq);
  res.steps.push(checkStep(E,uniq));
  return res;
}

/* ================= quadratic formula ================= */
function ca(h){ return '<span class="va">'+h+'</span>'; }
function cb(h){ return '<span class="vb">'+h+'</span>'; }
function cc(h){ return '<span class="vc">'+h+'</span>'; }
function coloredStd(A,B,C){
  var out='', cls=[ca,cb,cc], v=[A,B,C], vars=[X+'\u00b2',X,''];
  for(var i=0;i<3;i++){
    if(v[i].n===0) continue;
    var mag=abs(v[i]), text=termText(mag,vars[i]);
    if(!out) out=cls[i]((v[i].n<0 ? MINUS : '')+text);
    else out+=' '+cls[i]((v[i].n<0 ? MINUS+' ' : '+ ')+text);
  }
  return out+' = 0';
}
function radTerm(s,t){ return t===1 ? ''+s : (s===1 ? '' : s)+'\u221a'+t; }
function radExpr(P,S,t,Dn,sign,keepZero){
  var rt=radTerm(S,t), sym= sign==='+' ? '+' : (sign==='-' ? MINUS : '\u00b1'), body;
  if(P===0 && !keepZero) body=(sign==='+' ? '' : sym)+rt;
  else body=fmt(F(P))+' '+sym+' '+rt;
  if(Dn===1) return body;
  var den = Dn<0 ? '('+MINUS+Math.abs(Dn)+')' : ''+Dn;
  return (P===0 && !keepZero) ? body+' / '+den : '('+body+') / '+den;
}
function radVal(P,S,t,Dn,sign){ return (P+(sign==='+' ? 1 : -1)*S*Math.sqrt(t))/Dn; }
function reduceRad(P,S,Dn){
  var g=gcd(gcd(Math.abs(P),S),Math.abs(Dn)) || 1;
  var dv=g*(Dn<0 ? -1 : 1);
  return {P:P/dv, S:S/g, Dn:Dn/dv, dv:dv};
}

function buildQuad(E){
  var S=standardize(E,false);
  var res={eqHTML:eqText(E), steps:S.steps.slice(), answer:'', solNums:[], E:E};
  if(S.A.n===0) return notQuadratic(res,S);
  var A=S.A, B=S.B, C=S.C, a=A.n, b=B.n, c=C.n;
  var il=[T('The standard form is <i>ax</i>\u00b2 + <i>bx</i> + <i>c</i> = 0. Match your equation to it. Keep each sign with its number.'),
          M(coloredStd(A,B,C)),
          M('<span class="chips"><span class="chip va">a = '+fmt(A)+'</span><span class="chip vb">b = '+fmt(B)+'</span><span class="chip vc">c = '+fmt(C)+'</span></span>')];
  if(Math.abs(a)===1) il.push(T('There is no number written in front of '+X+'\u00b2, so <i>a</i> is '+fmt(A)+'.'));
  if(Math.abs(b)===1) il.push(T('There is no number written in front of '+X+', so <i>b</i> is '+fmt(B)+'.'));
  if(b===0) il.push(T('There is no '+X+' term, so <i>b</i> = 0.'));
  if(c===0) il.push(T('There is no constant term, so <i>c</i> = 0.'));
  res.steps.push({title:'Identify a, b, and c', lines:il});

  res.steps.push({title:'Write the quadratic formula', lines:[
    T('Here is the formula. The \u00b1 means you will get two answers: one using + and one using '+MINUS+'.'),
    M(X+' = ('+MINUS+cb('<i>b</i>')+' \u00b1 \u221a('+cb('<i>b</i>')+'\u00b2 '+MINUS+' 4'+ca('<i>a</i>')+cc('<i>c</i>')+')) / (2'+ca('<i>a</i>')+')')
  ]});

  var subLine=X+' = ('+MINUS+cb(par(B))+' \u00b1 \u221a('+cb(par(B)+'\u00b2')+' '+MINUS+' 4'+ca(par(A))+cc(par(C))+')) / (2'+ca(par(A))+')';
  res.steps.push({title:'Substitute the values', lines:[
    T('Replace each letter with its colored value. Use parentheses so the signs stay correct.'),
    M(subLine)
  ]});

  var b2=b*b, fac=4*a*c, D=b2-fac;
  var dl=[T('Work on the part under the square root first. This part, <i>b</i>\u00b2 '+MINUS+' 4<i>ac</i>, is called the discriminant.'),
          M(cb(par(B)+'\u00b2')+' '+MINUS+' 4'+ca(par(A))+cc(par(C))),
          M('= '+b2+' '+MINUS+' '+parNeg(F(fac)))];
  if(fac<0) dl.push(M('= '+b2+' + '+Math.abs(fac)));
  dl.push(M('= '+fmt(F(D))));
  if(D<0){
    dl.push(T('The discriminant is negative. You can\u2019t take the square root of a negative number, so this equation has <b>no real solutions</b>. (Its graph never touches the '+X+'-axis.)'));
    res.steps.push({title:'Simplify the discriminant', gives:true, lines:dl});
    res.answer='No real solutions';
    return res;
  }
  dl.push(T(D===0 ? 'The discriminant is 0, so there will be only one solution.' : 'The discriminant is positive, so there will be two solutions.'));
  var P=-b, Dn=2*a;
  dl.push(T('Put it back into the formula and simplify the other parts:'));
  dl.push(M(X+' = ('+cb(fmt(F(P)))+' \u00b1 \u221a'+D+') / '+ca(parNeg(F(Dn)))));
  res.steps.push({title:'Simplify the discriminant', lines:dl});

  var sols=[], sd=Math.round(Math.sqrt(D));
  var rational=(sd*sd===D);
  if(D===0){
    var one=F(P,Dn);
    res.steps.push({title:'Find the solution', gives:true, lines:[
      T('\u221a0 = 0, so the \u00b1 changes nothing:'),
      M(X+' = '+fmt(F(P))+' / '+parNeg(F(Dn))+' = '+fmt(one))
    ]});
    sols=[one];
    res.answer=ansText(sols);
    res.solNums=[num(one)];
    res.steps.push(checkStep(E,sols));
    return res;
  }
  if(rational){
    var l2=[T('\u221a'+D+' = '+sd+', so:'), M(X+' = ('+cb(fmt(F(P)))+' \u00b1 '+sd+') / '+ca(parNeg(F(Dn))))];
    res.steps.push({title:'Take the square root', lines:l2});
    var s1=F(P+sd,Dn), s2=F(P-sd,Dn);
    var fl=[T('Do the + and the '+MINUS+' separately:')];
    [['+',sd,s1],['\u2212',-sd,s2]].forEach(function(z){
      var numr=P+z[1];
      var line=X+' = ('+fmt(F(P))+' '+z[0]+' '+sd+') / '+parNeg(F(Dn))+' = '+fmt(F(numr))+' / '+parNeg(F(Dn))+' = '+fmt(z[2]);
      fl.push(M(line));
    });
    res.steps.push({title:'Find both solutions', gives:true, lines:fl});
    sols=sortF([s1,s2]);
    if(eq(sols[0],sols[1])) sols=[sols[0]];
    res.answer=ansText(sols);
    res.solNums=sols.map(num);
    res.steps.push(checkStep(E,sols));
    return res;
  }
  var sr=simpRad(D);
  var rl=[];
  if(sr.s>1){
    rl.push(T('\u221a'+D+' is not a whole number. Simplify it by finding the largest perfect square that divides '+D+':'));
    rl.push(M('\u221a'+D+' = \u221a('+(sr.s*sr.s)+' \u00b7 '+sr.t+') = '+sr.s+'\u221a'+sr.t));
  } else {
    rl.push(T('\u221a'+D+' is not a whole number, and '+D+' has no perfect-square factor, so it stays as \u221a'+D+'.'));
  }
  rl.push(M(X+' = ('+cb(fmt(F(P)))+' \u00b1 '+radTerm(sr.s,sr.t)+') / '+ca(parNeg(F(Dn)))));
  res.steps.push({title:'Simplify the square root', lines:rl});

  var rd=reduceRad(P,sr.s,Dn);
  var fl2=[];
  if(rd.dv!==1){
    fl2.push(T('Divide every number (in the numerator and the denominator) by '+fmt(F(rd.dv))+(rd.dv<0 ? ' to make the denominator positive' : '')+':'));
    fl2.push(M(X+' = '+radExpr(rd.P,rd.S,sr.t,rd.Dn,'\u00b1')));
  }
  fl2.push(T('Write the two solutions separately. Use a calculator for decimal approximations:'));
  var vp=radVal(rd.P,rd.S,sr.t,rd.Dn,'+'), vm=radVal(rd.P,rd.S,sr.t,rd.Dn,'-');
  fl2.push(M(X+' = '+radExpr(rd.P,rd.S,sr.t,rd.Dn,'+')+' \u2248 '+fmtN(vp)));
  fl2.push(M(X+' = '+radExpr(rd.P,rd.S,sr.t,rd.Dn,'-')+' \u2248 '+fmtN(vm)));
  res.steps.push({title:'Find both solutions', gives:true, lines:fl2});
  res.answer=X+' = '+radExpr(rd.P,rd.S,sr.t,rd.Dn,'+')+' \u2248 '+fmtN(vp)+'  or  '+X+' = '+radExpr(rd.P,rd.S,sr.t,rd.Dn,'-')+' \u2248 '+fmtN(vm);
  res.solNums=[vp,vm];
  res.steps.push({title:'Check your answers', lines:[
    T('These answers have square roots, so check them with a calculator: put each decimal into the original equation. Both sides should come out (almost) equal.')
  ]});
  return res;
}

/* ================= square roots ================= */
function buildSqrt(E){
  var a=E.a, hs=E.hs, c=E.c, e=E.e, d=E.d;
  var U=sqrtExprInner(hs), steps=[];
  var res={eqHTML:eqText(E), steps:steps, answer:'', solNums:[], E:E};
  var A2=a, rhs=d, lines;
  function sqEq(coef,cst,right){ return sqSide(coef,hs,cst)+' = '+right; }
  if(nonzero(e)){
    A2=sub(a,e);
    steps.push({title:'Get the squared parts on one side', lines:[
      T('Subtract '+(eq(e,F(1)) ? sqSquared(hs) : fmt(e)+sqSquared(hs))+' from both sides so the squared part is only on the left:'),
      M(sqEq(A2,c,fmt(d)))
    ]});
  }
  lines=[];
  var cur=rhs;
  if(nonzero(c)){
    lines.push(T((c.n>0 ? 'Subtract ' : 'Add ')+fmt(abs(c))+(c.n>0 ? ' from' : ' to')+' both sides:'));
    cur=sub(d,c);
    lines.push(M(sqEq(A2,F(0),fmt(cur))));
  }
  var k=div(cur,A2);
  if(!eq(A2,F(1))){
    lines.push(T('Divide both sides by '+fmt(A2)+':'));
    lines.push(M(sqEq(F(1),F(0),fmt(k))));
  }
  if(lines.length) steps.push({title:'Get the squared part by itself', lines:lines});
  if(sgn(k)<0){
    steps.push({title:'Look at the result', gives:true, lines:[
      T('A squared number can never be negative, but this equation says it equals '+fmt(k)+'. So there are <b>no real solutions</b>.')
    ]});
    res.answer='No real solutions';
    return res;
  }
  if(k.n===0){
    var only=neg(hs);
    steps.push({title:'Take the square root', lines:[
      T('The squared part equals 0, and the only number that squares to 0 is 0:'),
      M(U+' = 0')
    ]});
    steps.push({title:'Solve for '+X, gives:true, lines:[M(X+' = '+fmt(only))]});
    res.answer=ansText([only]);
    res.solNums=[num(only)];
    steps.push(checkStep(E,[only]));
    return res;
  }
  var kText = isInt(k) ? fmt(k) : '('+fmt(k)+')';
  var tl=[T('Remember the \u00b1: a positive number and a negative number both give '+fmt(k)+' when squared.'),
          M(U+' = \u00b1\u221a'+kText)];
  var r=sqrtFrac(k), rr=null;
  if(r){
    tl.push(M(U+' = \u00b1'+fmt(r)));
  } else {
    var radicand=k.n*k.d, simp=simpRad(radicand);
    if(k.d===1){
      if(simp.s>1){
        tl.push(T('Simplify the radical by finding the largest perfect square that divides '+k.n+':'));
        tl.push(M('\u221a'+k.n+' = \u221a('+(simp.s*simp.s)+' \u00b7 '+simp.t+') = '+simp.s+'\u221a'+simp.t));
      } else {
        tl.push(T(k.n+' has no perfect-square factor, so \u221a'+k.n+' can\u2019t be simplified. It stays as \u221a'+k.n+'.'));
      }
      tl.push(M(U+' = \u00b1'+radTerm(simp.s,simp.t)));
    } else {
      tl.push(T('Rewrite so there is no square root in the denominator: \u221a(<i>n</i>/<i>d</i>) = \u221a(<i>nd</i>) / <i>d</i>.'));
      tl.push(M('\u221a'+kText+' = \u221a'+radicand+' / '+k.d+(simp.s>1 ? ' = '+radTerm(simp.s,simp.t)+' / '+k.d : '')));
      tl.push(M(U+' = \u00b1'+radTerm(simp.s,simp.t)+' / '+k.d));
    }
    rr=simp;
  }
  steps.push({title:'Take the square root of both sides', lines:tl});
  var sl=[], sols=[];
  if(r){
    if(hs.n===0){
      sl.push(M(X+' = \u00b1'+fmt(r)));
    } else {
      sl.push(T('Now solve for '+X+' using both the positive and the negative value:'));
    }
    [r,neg(r)].forEach(function(v){
      var x=sub(v,hs); sols.push(x);
      if(hs.n!==0) sl.push(M(U+' = '+fmt(v)+'   \u2192   '+X+' = '+fmt(v)+' '+(hs.n>0 ? MINUS : '+')+' '+fmt(abs(hs))+' = '+fmt(x)));
    });
    sols=sortF(sols);
    res.answer=ansText(sols);
    res.solNums=sols.map(num);
    steps.push({title:'Solve for '+X, gives:true, lines:sl});
    steps.push(checkStep(E,sols));
  } else {
    var P=-hs.n*k.d, simp2=rr, Dn=k.d;
    var rd=reduceRad(P,simp2.s,Dn);
    if(hs.n!==0){
      sl.push(T((hs.n>0 ? 'Subtract '+fmt(hs)+' from' : 'Add '+fmt(abs(hs))+' to')+' both sides to get '+X+' by itself:'));
    } else sl.push(T('The solutions are the positive and negative square roots:'));
    sl.push(M(X+' = '+radExpr(P,simp2.s,simp2.t,Dn,'\u00b1')));
    if(rd.dv!==1 && Dn>1){
      sl.push(T('Divide every number by '+rd.dv+' to simplify:'));
      sl.push(M(X+' = '+radExpr(rd.P,rd.S,simp2.t,rd.Dn,'\u00b1')));
    }
    var vp=radVal(rd.P,rd.S,simp2.t,rd.Dn,'+'), vm=radVal(rd.P,rd.S,simp2.t,rd.Dn,'-');
    sl.push(T('Use a calculator for decimal approximations:'));
    sl.push(M(X+' = '+radExpr(rd.P,rd.S,simp2.t,rd.Dn,'+')+' \u2248 '+fmtN(vp)));
    sl.push(M(X+' = '+radExpr(rd.P,rd.S,simp2.t,rd.Dn,'-')+' \u2248 '+fmtN(vm)));
    steps.push({title:'Solve for '+X, gives:true, lines:sl});
    res.answer=X+' = '+radExpr(rd.P,rd.S,simp2.t,rd.Dn,'+')+' \u2248 '+fmtN(vp)+'  or  '+X+' = '+radExpr(rd.P,rd.S,simp2.t,rd.Dn,'-')+' \u2248 '+fmtN(vm);
    res.solNums=[vp,vm];
    steps.push({title:'Check your answers', lines:[
      T('These answers have square roots, so check them with a calculator: put each decimal into the original equation. Both sides should come out (almost) equal.')
    ]});
  }
  return res;
}

/* ================= problem generators ================= */
function ri(a,b){ return Math.floor(Math.random()*(b-a+1))+a; }
function nzr(a,b){ var v=0; while(v===0) v=ri(a,b); return v; }
function pick(arr){ return arr[ri(0,arr.length-1)]; }
var lastKey='';
function isSquare(n){ var r=Math.round(Math.sqrt(n)); return r*r===n; }
function tryGen(fn){
  var E=null, i, key;
  for(i=0;i<800;i++){
    E=fn(); if(!E) continue;
    key=eqText(E);
    if(key===lastKey) continue;
    lastKey=key; return E;
  }
  while(!E) E=fn();
  return E;
}
function polyEq(L,R){ return {kind:'poly', L:L.map(function(v){ return F(v); }), R:R.map(function(v){ return F(v); })}; }
function sizeOK(vals){ return vals.every(function(v){ return Math.abs(v)<=60; }); }
function divisorsOf(n){ var o=[]; for(var i=1;i<=n;i++) if(n%i===0) o.push(i); return o; }

/* factor builders return {p,q,r,s} meaning (px+q)(rx+s) */
var EASY_C=[2,3,5,6,7,8,9,10,12,14,15];
function easyFactors(){
  for(;;){
    var q,s,m,n,p;
    if(Math.random()<0.6){
      var cAbs=pick(EASY_C); m=pick(divisorsOf(cAbs)); n=cAbs/m;
      var sp=pick([[1,1],[-1,-1],[1,-1],[-1,1]]);
      q=m*sp[0]; s=n*sp[1];
      if(q+s===0 || q===s) continue;
      return {p:1,q:q,r:1,s:s};
    }
    p=pick([2,3]);
    var cAbs2=pick([2,3,5,6,7,10]);
    m=pick(divisorsOf(cAbs2)); n=cAbs2/m;
    var sp2=pick([[1,1],[-1,-1],[1,-1],[-1,1]]);
    q=m*sp2[0]; s=n*sp2[1];
    if(Math.random()<0.5){ var tmp=q; q=s; s=tmp; }
    if(gcd(p,Math.abs(q))!==1) continue;
    if(p*s+q===0) continue;
    return {p:p,q:q,r:1,s:s};
  }
}
function mediumFactors(){
  for(;;){
    var p=pick([1,1,2,3]), q=nzr(-9,9), s=nzr(-9,9);
    if(gcd(p,Math.abs(q))!==1) continue;
    if(p*s+q===0) continue;
    return {p:p,q:q,r:1,s:s};
  }
}
function hardFactors(){
  var pairs=[[1,1],[2,1],[3,1],[2,2],[4,1],[3,2],[6,1]];
  for(;;){
    var pr=pick(pairs), p=pr[0], r=pr[1], q=nzr(-10,10), s=nzr(-10,10);
    if(gcd(p,Math.abs(q))!==1 || gcd(r,Math.abs(s))!==1) continue;
    var A=p*r, B=p*s+q*r, C=q*s;
    if(B===0 || A>6 || gcd(gcd(A,Math.abs(B)),Math.abs(C))!==1) continue;
    return {p:p,q:q,r:r,s:s};
  }
}
function trinomial(f){ return [f.p*f.r, f.p*f.s+f.q*f.r, f.q*f.s]; }

function disguise(tri, level, mode){
  var A=tri[0], B=tri[1], C=tri[2];
  if(mode==='M1') return polyEq([A,B,0],[0,0,-C]);
  if(mode==='M2') return polyEq([A,0,0],[0,-B,-C]);
  if(mode==='M3') return polyEq([A,0,C],[0,-B,0]);
  if(mode==='M5'){ var r=nzr(-9,9); return polyEq([A,B,C+r],[0,0,r]); }
  if(mode==='both'){
    var p=pick([0,1,2]), q=nzr(-8,8), r2=nzr(-8,8);
    return polyEq([A+p,B+q,C+r2],[p,q,r2]);
  }
  if(mode==='xprod') return {kind:'xprod', b:F(B), rhs:F(-C)};
  if(mode==='prod'){
    var m=nzr(-6,6), n=B-m;
    if(n===0) return null;
    var e=m*n-C;
    if(e===0 || Math.abs(e)>60) return null;
    return {kind:'prod', m:F(m), n:F(n), rhs:F(e)};
  }
  if(mode==='gcf'){ var k=pick([2,3,4]); return polyEq([k*A,k*B,k*C],[0,0,0]); }
  return polyEq([A,B,C],[0,0,0]);
}

function genFactoring(level){
  return tryGen(function(){
    var f, tri, mode;
    if(level==='easy'){ f=easyFactors(); tri=trinomial(f); mode='std'; }
    else if(level==='medium'){
      f=mediumFactors(); tri=trinomial(f);
      mode=pick(['M1','M2','M3','M5','M1','M2']);
      if(mode==='M3' && tri[1]===0) mode='M1';
    } else {
      mode=pick(['both','both','prod','xprod','gcf']);
      if(mode==='prod' || mode==='xprod') f={p:1,q:nzr(-9,9),r:1,s:nzr(-9,9)};
      else f=hardFactors();
      tri=trinomial(f);
      if(mode==='gcf' && tri[0]>3) mode='both';
      if((mode==='prod' || mode==='xprod') && tri[1]===0) return null;
    }
    if(tri[2]===0) return null;
    var E=disguise(tri,level,mode);
    if(!E) return null;
    if(E.kind==='poly' && !sizeOK(E.L.concat(E.R).map(num))) return null;
    return E;
  });
}

function genQuad(level){
  return tryGen(function(){
    var A,B,C,D,E,t,f;
    if(level==='easy'){
      var r1=nzr(-8,8), r2=nzr(-8,8);
      if(r1===r2) return null;
      return disguise([1,-(r1+r2),r1*r2],level,'std');
    }
    if(level==='medium'){
      if(Math.random()<0.5){
        A=1; B=ri(-8,8); C=ri(-10,10); D=B*B-4*C;
        if(D<=0 || isSquare(D)) return null;
      } else {
        f=mediumFactors(); if(f.p===1) return null;
        t=trinomial(f); A=t[0]; B=t[1]; C=t[2];
      }
      E=disguise([A,B,C],level,pick(['std','std','std','M1','M2']));
    } else {
      if(Math.random()<0.12){
        var rt=nzr(-6,6); A=pick([1,2,3,-1,-2]); B=-2*A*rt; C=A*rt*rt;
        E=disguise([A,B,C],level,pick(['std','both','M1']));
        return (E.kind==='poly' && !sizeOK(E.L.concat(E.R).map(num))) ? null : E;
      }
      A=pick([-1,-2,2,3,4,5,-3]); B=ri(-12,12); C=ri(-12,12);
      if(B===0 && C===0) return null;
      D=B*B-4*A*C;
      if(D<0) return null;
      if(D===0){ if(Math.random()<0.7) return null; }
      else if(isSquare(D) && Math.random()<0.8) return null;
      E=disguise([A,B,C],level,pick(['std','both','M1','M2','both']));
    }
    if(!E) return null;
    if(E.kind==='poly' && !sizeOK(E.L.concat(E.R).map(num))) return null;
    return E;
  });
}

function sqrtEq(a,hs,c,e,d){ return {kind:'sqrt', a:F(a), hs:F(hs), c:F(c), e:F(e), d:F(d)}; }
function nonSquareInt(lo,hi){ var k; do { k=ri(lo,hi); } while(isSquare(k)); return k; }
function genSqrt(level){
  return tryGen(function(){
    var t=Math.random(), n, a, c, hs, k, ee, E;
    if(level==='easy'){
      if(t<0.15){ n=ri(2,12); E=sqrtEq(1,0,0,0,n*n); }
      else if(t<0.45){ n=ri(2,12); c=nzr(-12,12); E=sqrtEq(1,0,c,0,n*n+c); }
      else if(t<0.7){
        if(Math.random()<0.5){ a=pick([2,3,4,5]); n=ri(2,9); E=sqrtEq(a,0,0,0,a*n*n); }
        else {
          var mm=pick([2,3,4,5]), nn=ri(1,9);
          if(gcd(mm,nn)!==1 || nn===mm) return null;
          E=sqrtEq(mm*mm,0,0,0,nn*nn);
        }
      }
      else { a=pick([2,3,4,5]); n=ri(2,8); c=nzr(-12,12); E=sqrtEq(a,0,c,0,a*n*n+c); }
    } else if(level==='medium'){
      if(t<0.35){
        a=pick([1,1,2,3,4,5]); k=nonSquareInt(2,40);
        c = a===1 ? pick([0,nzr(-9,9)]) : nzr(-9,9);
        E=sqrtEq(a,0,c,0,a*k+c);
      } else if(t<0.55){ n=ri(1,10); hs=nzr(-8,8); E=sqrtEq(1,hs,0,0,n*n); }
      else { a=pick([2,3,4]); n=ri(1,8); c=nzr(-10,10); hs=nzr(-8,8); E=sqrtEq(a,hs,c,0,a*n*n+c); }
    } else {
      if(t<0.35){ a=pick([2,3,4,5]); k=nonSquareInt(2,30); c=nzr(-12,12); hs=ri(-8,8); E=sqrtEq(a,hs,c,0,a*k+c); }
      else if(t<0.6){ k=nonSquareInt(2,40); c=nzr(-12,12); hs=nzr(-8,8); E=sqrtEq(1,hs,c,0,k+c); }
      else {
        ee=pick([1,2,3]); a=ee+pick([1,2,3]); c=nzr(-12,12); hs=pick([0,0,nzr(-6,6)]);
        k = Math.random()<0.5 ? pick([4,9,16,25]) : nonSquareInt(2,25);
        E=sqrtEq(a,hs,c,ee,c+(a-ee)*k);
      }
    }
    var big=[E.a,E.c,E.e,E.d].some(function(v){ return Math.abs(num(v))>200; });
    return big ? null : E;
  });
}

/* ================= tool settings ================= */
var TOOLS={
  factoring:{
    title:'Solving by factoring',
    lede:'Solve quadratic equations by factoring and using the zero product property. Reveal one step at a time, or check just the answer.',
    task:'Solve for <i>x</i> by factoring.',
    notes:{
      easy:'Already set equal to 0. a is 1, 2, or 3, and c is a prime or a number with few factors.',
      medium:'Not set equal to 0 yet, so terms need to be moved first. a can be 1, 2, or 3.',
      hard:'Moving terms from both sides, multiplying out parentheses, or dividing out a common factor.',
      custom:'Type in an equation from your homework and see the steps.'
    },
    gen:genFactoring, build:buildFactoring,
    entryHint:'Type the left side, then the right side. Leave the number in front of x\u00b2 or x blank if it is 1. Leave a right-side box blank if it is 0. If the problem has parentheses, multiply them out first.',
    entry:[{id:'a',sign:true,blank:1},{html:'<i>x</i>\u00b2'},{id:'b',sign:true,blank:1},{html:'<i>x</i>'},{id:'c',sign:true,blank:0},
           {html:' = '},{id:'d',sign:true,blank:0},{html:'<i>x</i>\u00b2'},{id:'e',sign:true,blank:0},{html:'<i>x</i>'},{id:'f',sign:true,blank:0}],
    fromEntry:function(v){ return {kind:'poly', L:[v.a,v.b,v.c], R:[v.d,v.e,v.f]}; }
  },
  quadformula:{
    title:'Solving with the quadratic formula',
    lede:'Walk through the quadratic formula one step at a time. The values of a, b, and c are color-coded so you can see where each one goes.',
    task:'Solve for <i>x</i> using the quadratic formula.',
    notes:{
      easy:'Already set equal to 0, with a = 1 and whole-number answers.',
      medium:'Answers with square roots when a = 1, or fraction answers when a is 2 or 3. Sometimes terms need to be moved first.',
      hard:'Larger or negative a, simplifying radicals, reducing fractions, and equations that need rearranging.',
      custom:'Type in an equation from your homework and see each step.'
    },
    gen:genQuad, build:buildQuad,
    entryHint:'Type the left side, then the right side. Leave the number in front of x\u00b2 or x blank if it is 1. Leave a right-side box blank if it is 0.',
    entry:[{id:'a',sign:true,blank:1},{html:'<i>x</i>\u00b2'},{id:'b',sign:true,blank:1},{html:'<i>x</i>'},{id:'c',sign:true,blank:0},
           {html:' = '},{id:'d',sign:true,blank:0},{html:'<i>x</i>\u00b2'},{id:'e',sign:true,blank:0},{html:'<i>x</i>'},{id:'f',sign:true,blank:0}],
    fromEntry:function(v){ return {kind:'poly', L:[v.a,v.b,v.c], R:[v.d,v.e,v.f]}; }
  },
  sqrt:{
    title:'Solving with square roots',
    lede:'Get the squared part by itself, take the square root of both sides, and remember the \u00b1. Reveal one step at a time, or check just the answer.',
    task:'Solve for <i>x</i> using square roots.',
    notes:{
      easy:'One- and two-step problems with whole-number or fraction answers.',
      medium:'Answers with square roots, plus problems like 2(x \u2212 1)\u00b2 + 3 = 21 with whole-number answers.',
      hard:'More square-root answers, squared parts on both sides, and extra steps.',
      custom:'Type in an equation from your homework and see the steps.'
    },
    gen:genSqrt, build:buildSqrt,
    entryHint:'Use the form a(x + h)\u00b2 + c = d. Leave the number in front blank if it is 1. Leave the h box blank if the problem has just x\u00b2.',
    entry:[{id:'a',sign:true,blank:1},{html:'(<i>x</i>'},{id:'h',sign:true,blank:0},{html:')\u00b2'},{id:'c',sign:true,blank:0},{html:' = '},{id:'d',sign:true,blank:0}],
    fromEntry:function(v){ return {kind:'sqrt', a:v.a, hs:v.h, c:v.c, e:F(0), d:v.d}; }
  }
};
var tool=TOOLS[TOOL];
var LEVELS=['easy','medium','hard','custom'];
var LEVEL_NAMES={easy:'Easy',medium:'Medium',hard:'Hard',custom:'Custom'};

/* ================= page ================= */
var state={level:'easy', res:null, shown:0, ansShown:false, csigns:{}};
function $(s){ return document.querySelector(s); }

function buildShell(){
  document.title=tool.title;
  var row='';
  tool.entry.forEach(function(t){
    if(t.html){ row+='<span>'+t.html+'</span>'; return; }
    state.csigns[t.id]=1;
    row+='<button type="button" class="csign" data-id="'+t.id+'" id="s-'+t.id+'" aria-label="Sign for '+t.id+': plus. Tap to switch.">+</button>'+
      '<input id="in-'+t.id+'" data-id="'+t.id+'" inputmode="numeric" maxlength="3" autocomplete="off" placeholder="'+t.blank+'" aria-label="Number for '+t.id+'">';
  });
  $('#app').innerHTML =
    '<a class="back" href="../">\u2190 All quadratics tools</a>'+
    '<h1>'+tool.title+'</h1>'+
    '<p class="lede">'+tool.lede+'</p>'+
    '<div class="bar"><div class="levels" role="group" aria-label="Difficulty">'+
      LEVELS.map(function(l){ return '<button type="button" data-level="'+l+'" aria-pressed="false">'+LEVEL_NAMES[l]+'</button>'; }).join('')+
    '</div><button type="button" class="ghost" id="big" aria-pressed="false">Large text for projecting</button></div>'+
    '<p class="note" id="levelNote"></p>'+
    '<section class="panel custom" id="customPanel" hidden><h2>Check a homework problem</h2>'+
      '<p class="sub">'+tool.entryHint+'</p><div class="centry">'+row+'</div>'+
      '<button type="button" class="btn primary" id="cgo">Use this problem</button><p class="cmsg" id="cmsg" role="alert"></p></section>'+
    '<section class="sheet" aria-labelledby="probLabel"><p class="label" id="probLabel">'+tool.task+'</p>'+
      '<p class="problem" id="problem"></p></section>'+
    '<div class="controls" id="controls" role="group" aria-label="Show or hide the work">'+
      '<button type="button" class="btn primary" id="next">Show next step</button>'+
      '<button type="button" class="btn" id="allSteps">Show all steps</button>'+
      '<button type="button" class="btn" id="ansOnly">Show answer only</button>'+
      '<button type="button" class="btn" id="hideAll">Hide all</button>'+
      '<button type="button" class="btn" id="newp">New problem</button></div>'+
    '<p class="progress" id="progress" aria-live="polite"></p>'+
    '<div class="steps" id="steps"></div>'+
    '<section class="answer-box" id="answer" hidden aria-live="polite"><h2>Solution</h2><p class="final" id="final"></p></section>';
}

function setLevelButtons(){
  document.querySelectorAll('.levels button').forEach(function(b){
    b.setAttribute('aria-pressed', String(b.dataset.level===state.level));
  });
  $('#levelNote').textContent=tool.notes[state.level];
  $('#customPanel').hidden = state.level!=='custom';
  $('#newp').textContent = state.level==='custom' ? 'Enter another problem' : 'New problem';
}

function givesIndex(){
  var r=state.res; if(!r) return -1;
  for(var i=0;i<r.steps.length;i++) if(r.steps[i].gives) return i;
  return r.steps.length-1;
}

function render(){
  var r=state.res;
  $('#problem').innerHTML = r ? r.eqHTML : '<span class="empty">Enter an equation above to begin.</span>';
  $('#controls').hidden = !r;
  $('#progress').hidden = !r;
  if(!r){ $('#steps').innerHTML=''; $('#answer').hidden=true; return; }
  var N=r.steps.length;
  var html='';
  for(var i=0;i<state.shown;i++){
    var st=r.steps[i];
    html+='<article class="step"><h2><span class="n">'+(i+1)+'.</span>'+st.title+'</h2>'+
      st.lines.map(function(l){ return l.t!==undefined ? '<p class="st">'+l.t+'</p>' : '<p class="sm">'+l.m+'</p>'; }).join('')+'</article>';
  }
  $('#steps').innerHTML=html;
  var gi=givesIndex();
  var showAns = state.ansShown || state.shown>gi;
  $('#answer').hidden=!showAns;
  $('#final').innerHTML=r.answer;
  $('#progress').textContent='Steps shown: '+state.shown+' of '+N+(showAns ? '.  Answer shown.' : '.');
  $('#next').disabled = state.shown>=N;
  $('#allSteps').disabled = state.shown>=N && showAns;
}

function loadProblem(E){
  state.res = E ? tool.build(E) : null;
  state.shown=0; state.ansShown=false;
  render();
}

function readEntry(){
  var vals={};
  for(var i=0;i<tool.entry.length;i++){
    var t=tool.entry[i];
    if(!t.id) continue;
    var raw=$('#in-'+t.id).value.trim();
    var v = raw==='' ? F(t.blank) : F(parseInt(raw,10));
    vals[t.id]=mul(v,F(state.csigns[t.id]));
  }
  if(TOOL==='sqrt'){
    if(vals.a.n===0) return {err:'The number in front (a) can\u2019t be 0.'};
  }
  return {vals:vals};
}
function useCustom(){
  var r=readEntry();
  if(r.err){ $('#cmsg').textContent=r.err; return; }
  $('#cmsg').textContent='';
  loadProblem(tool.fromEntry(r.vals));
}
function newProblem(){
  setLevelButtons();
  if(state.level==='custom'){
    $('#cmsg').textContent='';
    Object.keys(state.csigns).forEach(function(id){
      state.csigns[id]=1;
      var b=$('#s-'+id); b.textContent='+'; b.setAttribute('aria-label','Sign for '+id+': plus. Tap to switch.');
      $('#in-'+id).value='';
    });
    loadProblem(null);
    var f=$('#in-a'); if(f) f.focus({preventScroll:true});
    return;
  }
  loadProblem(tool.gen(state.level));
}

document.addEventListener('click', function(e){
  var t=e.target; if(!(t instanceof Element)) return;
  var lv=t.closest('.levels button');
  if(lv){ state.level=lv.dataset.level; newProblem(); return; }
  if(t.closest('#big')){
    var on=document.documentElement.classList.toggle('big');
    $('#big').setAttribute('aria-pressed', String(on)); return;
  }
  if(t.closest('#next')){ if(state.res && state.shown<state.res.steps.length){ state.shown++; render(); } return; }
  if(t.closest('#allSteps')){ if(state.res){ state.shown=state.res.steps.length; state.ansShown=true; render(); } return; }
  if(t.closest('#ansOnly')){ state.ansShown=true; render(); return; }
  if(t.closest('#hideAll')){ state.shown=0; state.ansShown=false; render(); return; }
  if(t.closest('#newp')) return newProblem();
  var cs=t.closest('button.csign');
  if(cs){
    var id=cs.dataset.id; state.csigns[id]*=-1;
    var plus=state.csigns[id]===1;
    cs.textContent=plus ? '+' : '\u2212';
    cs.setAttribute('aria-label','Sign for '+id+': '+(plus ? 'plus' : 'minus')+'. Tap to switch.');
    return;
  }
  if(t.closest('#cgo')) return useCustom();
});
document.addEventListener('input', function(e){
  var el=e.target;
  if(el.closest && el.closest('.centry') && el.tagName==='INPUT') el.value=el.value.replace(/[^0-9]/g,'');
});
document.addEventListener('focusin', function(e){
  var el=e.target;
  if(el.closest && el.closest('.centry') && el.tagName==='INPUT'){ try{ el.select(); }catch(err){} }
});
document.addEventListener('keydown', function(e){
  if(e.key==='Enter' && e.target.closest && e.target.closest('.centry') && e.target.tagName==='INPUT'){
    e.preventDefault(); useCustom();
  }
});

buildShell();
newProblem();

window.SolveTools={F:F,fmt:fmt,gen:tool.gen,build:tool.build,eqText:eqText,evalNum:evalNum,state:state,num:num,
  levels:LEVELS, standardize:standardize};
})();
