/-  gene
|.
=>  $:gene
=*  sack  +3
=*  moan  moan.sack
=*  cole  cole.sack
=|  =fuji
=>
|%
+$  nogs
  $:  ali=(map @uvre @uvre)
      cel=(set @uvre)
      dad=(map [@uvre @uvre] @uvre)
      hed=(map @uvre @uvre)
      tel=(map @uvre @uvre)
      lit=(map @uvre *)
      def=(map @uvre (pair @uwoo (each pole site)))
      use=(jar @uvre (pair @uwoo (each pole site)))
  ==
::
++  heed
  |=  s=site
  ^-  (list @uwoo)
  ?+  -.s  ~
    %clq  ~[z.s o.s]
    %eqq  ~[z.s o.s]
    %brn  ~[z.s o.s]
    %hop  ~[t.s]
    %hip  ~[t.s]
    %lnk  ~[t.s]
    %cal  ~[t.s]
    %caf  ~[t.s]
    %spy  ~[t.s]
    %mer  ~[i.s m.s]
  ==
::
++  py
  |_  p=pile
  ::
  ++  bake
    ^+  p
    =.  p  fuse
    ::  XX temporary: turn hip/phi into mov so we can run this as-is
    ::  note that it's not safe to do mov coalescing on the output of this
    ::  since we may now have multiple %mov's that target one register
    ::
    defi
  ::
  ++  defi
    ^+  p
    =|  back=(list @uwoo)
    =/  queu=(list @uwoo)  [0w0 0w1 ~]
    =/  seen  (~(gas in *(set @uwoo)) queu)
    |-  ^+  p
    ?~  queu
      ?~  back  p
      $(queu (flop back), back ~)
    =/  blob  (~(got by will.p) i.queu)
    ::
    =?  will.p  ?=(%hip -.bend.blob)
      %+  ~(put by will.p)  i.queu
      =/  movs
        %-  ~(rep by biff:(~(got by will.p) t.bend.blob))
        |=  [[out=@uvre bin=(map @uwoo @uvre)] lit=(list pole)]
        [[%mov (~(got by bin) c.bend.blob) out] lit]
      [biff.blob (welp body.blob movs) %hop t.bend.blob]  :: XX flop?
    ::
    =/  more  (skip (heed bend.blob) ~(has in seen))
    %=  $
      queu  t.queu
      back  (weld more back)
      seen  (~(gas in seen) more)
    ==
  ::
  ++  from
    ^-  (jar @uwoo @uwoo)
    %-  ~(rep by will.p)
    |=  [[u=@uwoo b=blob] fum=(jar @uwoo @uwoo)]
    (roll (heed bend.b) |=([i=@uwoo =_fum] (~(add ja fum) i u)))
  ::
  ++  fuse
    =-  p(will -)
    ::  bogus entry prevents 0w1 from being coalesced into 0w0
    ::
    =/  fum  (~(put by from) 0w1 [0w0 0w0 ~])
    =/  wan  ^+(will.p ~)
    =|  bak=(list @uwoo)
    =/  for=(list @uwoo)  [0w0 0w1 ~]
    =/  hav  (~(gas in *(set @uwoo)) for)
    =|  nog=nogs  :: XX init [cel] &c from $need and/or $sock
    |-  ^+  wan
    ?~  for
      ?^  bak
        $(for (flop bak), bak ~)
      ?>(&((~(has by wan) 0w0) (~(has by wan) 0w1)) wan)
    =^  b  nog  (norm i.for nog (link i.for fum))
    =/  nex  (flop (skip (heed bend.b) ~(has in hav)))
    %=  $
      for  t.for
      wan  (~(put by wan) i.for b)
      bak  (weld nex bak)
      hav  (~(gas in hav) nex)
    ==
  ::
  ++  link
    |=  [i=@uwoo fum=(jar @uwoo @uwoo)]
    ^-  blob
    =/  b  (~(got by will.p) i)
    :-  biff.b
    |-  ^-  (pair (list pole) site)
    ?.  ?=(%hop -.bend.b)  +.b
    =/  tar  ~|  [missing=t.bend.b from=i ~(key by fum)]  (~(got by fum) t.bend.b)
    ?.  ?=([* ~] tar)  +.b
    ?>  =(i i.tar)
    =/  nex  $(b (~(got by will.p) t.bend.b), i t.bend.b)
    [(weld body.b p.nex) q.nex]
  ::
  ::  normalizing optimization
  ::
  ::    remove redundancy in registers, cons/decons, cell assertions,
  ::    construct def/use chains
  ::
  ++  norm
    |=  [u=@uwoo nog=nogs b=blob]
    =|  new=(list pole)
    |^  ^-  [blob nogs]
        ?~  body.b
          =^  s  nog  (bend bend.b)
          [b(body (flop new), bend s) nog]
        =^  p  nog  (body i.body.b)
        ?~  p
          $(body.b t.body.b)
        ?:  ?&  ?=(^ new)
                ?|  &(?=(%men -.i.new) ?=(%man -.u.p))
                    &(?=(%slo -.i.new) ?=(%sld -.u.p))
                    &(?=(%tim -.i.new) ?=(%tom -.u.p))
            ==  ==
          $(body.b t.body.b, new t.new)
        $(body.b t.body.b, new [u.p new])
    ::
    ++  body
      |=  p=pole
      ^-  [(unit pole) _nog]
      ?-    -.p
          %imm
        :-  `p
        %=  nog
          cel  ?@(n.p cel.nog (~(put in cel.nog) d.p))
          lit  (~(put by lit.nog) d.p n.p)
          def  (~(put by def.nog) d.p [u &+p])
        ==
      ::
          %mov
        =.  s.p  ?~(h=(~(get by ali.nog) s.p) s.p u.h)
        [~ nog(ali (~(put by ali.nog) d.p s.p))]
      ::
          %inc
        =.  s.p  ?~(h=(~(get by ali.nog) s.p) s.p u.h)
        :-  `p
        %=  nog
          def  (~(put by def.nog) d.p [u &+p])
          use  (~(add ja use.nog) s.p [u &+p])
        ==
      ::
          %con
        =.  h.p  ?~(h=(~(get by ali.nog) h.p) h.p u.h)
        =.  t.p  ?~(h=(~(get by ali.nog) t.p) t.p u.h)
        ?^  dad=(~(get by dad.nog) h.p t.p)
          [~ nog(ali (~(put by ali.nog) d.p u.dad))]
        :-  `p
        %=  nog
          cel  (~(put in cel.nog) d.p)
          dad  (~(put by dad.nog) [h.p t.p] d.p)
          hed  (~(put by hed.nog) d.p h.p)
          tel  (~(put by tel.nog) d.p t.p)
          def  (~(put by def.nog) d.p [u &+p])
          use  (~(add ja (~(add ja use.nog) h.p [u &+p])) t.p [u &+p])
        ==
      ::
          %hed
        =.  s.p  ?~(h=(~(get by ali.nog) s.p) s.p u.h)
        ?^  hed=(~(get by hed.nog) s.p)
          [~ nog(ali (~(put by ali.nog) d.p u.hed))]
        :-  `p
        =/  lit=(unit)
          ?~  dad=(~(get by lit.nog) s.p)  ~
          ?@(u.dad ~ `-.u.dad)
        %=  nog
          lit  ?~(lit lit.nog (~(put by lit.nog) d.p u.lit))
          cel  ?.(?=([~ ^] lit) cel.nog (~(put in cel.nog) d.p))
          hed  (~(put by hed.nog) s.p d.p)
          def  (~(put by def.nog) d.p [u &+p])
          use  (~(add ja use.nog) s.p [u &+p])
        ==
      ::
          %tal
        =.  s.p  ?~(h=(~(get by ali.nog) s.p) s.p u.h)
        ?^  tal=(~(get by tel.nog) s.p)
          [~ nog(ali (~(put by ali.nog) d.p u.tal))]
        :-  `p
        =/  lit=(unit)
          ?~  dad=(~(get by lit.nog) s.p)  ~
          ?@(u.dad ~ `+.u.dad)
        =/  hed  (~(get by hed.nog) s.p)
        %=  nog
          lit  ?~(lit lit.nog (~(put by lit.nog) d.p u.lit))
          cel  ?.(?=([~ ^] lit) cel.nog (~(put in cel.nog) d.p))
          dad  ?~(hed dad.nog (~(put by dad.nog) [u.hed d.p] s.p))
          tel  (~(put by tel.nog) s.p d.p)
          def  (~(put by def.nog) d.p [u &+p])
          use  (~(add ja use.nog) s.p [u &+p])
        ==
      ::
          %cel
        =.  p.p  ?~(h=(~(get by ali.nog) p.p) p.p u.h)
        ?:  (~(has in cel.nog) p.p)
          [~ nog]
        :-  `p
        %=  nog
          cel  (~(put in cel.nog) p.p)
          use  (~(add ja use.nog) p.p [u &+p])
        ==
      ::
          %men
        =.  s.p  ?~(h=(~(get by ali.nog) s.p) s.p u.h)
        [`p nog]
      ::
          ?(%slo %hit %slg)
        =.  s.p  ?~(h=(~(get by ali.nog) s.p) s.p u.h)
        [`p nog(use (~(add ja use.nog) s.p [u &+p]))]
      ::
          %mew
        =.  k.p  ?~(h=(~(get by ali.nog) k.p) k.p u.h)
        =.  u.p  ?~(h=(~(get by ali.nog) u.p) u.p u.h)
        =.  f.p  ?~(h=(~(get by ali.nog) f.p) f.p u.h)
        =.  r.p  ?~(h=(~(get by ali.nog) r.p) r.p u.h)
        =.  use.nog  (~(add ja use.nog) k.p [u &+p])
        =.  use.nog  (~(add ja use.nog) u.p [u &+p])
        =.  use.nog  (~(add ja use.nog) f.p [u &+p])
        =.  use.nog  (~(add ja use.nog) r.p [u &+p])
        [`p nog]
      ::
          ?(%man %sld %tim %tom %mem)
        [`p nog]
      ==
    ::
    ++  bend
      |=  s=site
      ^-  [site _nog]  :: XX only def and use, maybe cel
      ?-    -.s
          %clq
        =.  s.s  ?~(h=(~(get by ali.nog) s.s) s.s u.h)
        [s nog(use (~(add ja use.nog) s.s [u |+s]))] :: XX add ja cell for [z]
      ::
          %eqq
        =.  l.s  ?~(h=(~(get by ali.nog) l.s) l.s u.h)
        =.  r.s  ?~(h=(~(get by ali.nog) r.s) r.s u.h)
        =.  use.nog  (~(add ja use.nog) l.s [u |+s])
        =.  use.nog  (~(add ja use.nog) r.s [u |+s])
        [s nog]
      ::
          %brn
        =.  s.s  ?~(h=(~(get by ali.nog) s.s) s.s u.h)
        [s nog(use (~(add ja use.nog) s.s [u |+s]))]
      ::
          %lnk
        =.  u.s  ?~(h=(~(get by ali.nog) u.s) u.s u.h)
        =.  f.s  ?~(h=(~(get by ali.nog) f.s) f.s u.h)
        :-  s
        %=  nog
          def  (~(put by def.nog) d.s [u |+s])
          use  (~(add ja (~(add ja use.nog) u.s [u |+s])) f.s [u |+s])
        ==
      ::
          %cal
        =.  v.s  (turn v.s |=(a=@uvre ?~(h=(~(get by ali.nog) a) a u.h)))
        :-  s
        %=  nog
          def  (~(put by def.nog) d.s [u |+s])
          use  (roll v.s |=([a=@uvre use=_use.nog] (~(add ja use) a [u |+s])))
        ==
      ::
          %caf
        =.  v.s  (turn v.s |=(a=@uvre ?~(h=(~(get by ali.nog) a) a u.h)))
        =.  u.s  ?~(h=(~(get by ali.nog) u.s) u.s u.h)
        =.  use.nog  (~(add ja use.nog) u.s [u |+s])
        :-  s
        %=  nog
          def  (~(put by def.nog) d.s [u |+s])
          use  (roll v.s |=([a=@uvre use=_use.nog] (~(add ja use) a [u |+s])))
        ==
      ::
          %lnt
        =.  u.s  ?~(h=(~(get by ali.nog) u.s) u.s u.h)
        =.  f.s  ?~(h=(~(get by ali.nog) f.s) f.s u.h)
        :-  s
        %=  nog
          use  (~(add ja (~(add ja use.nog) u.s [u |+s])) f.s [u |+s])
        ==
      ::
          %jmp
        =.  v.s  (turn v.s |=(a=@uvre ?~(h=(~(get by ali.nog) a) a u.h)))
        :-  s
        %=  nog
          use  (roll v.s |=([a=@uvre use=_use.nog] (~(add ja use) a [u |+s])))
        ==
      ::
          %jmf
        =.  v.s  (turn v.s |=(a=@uvre ?~(h=(~(get by ali.nog) a) a u.h)))
        =.  u.s  ?~(h=(~(get by ali.nog) u.s) u.s u.h)
        =.  use.nog  (~(add ja use.nog) u.s [u |+s])
        :-  s
        %=  nog
          use  (roll v.s |=([a=@uvre use=_use.nog] (~(add ja use) a [u |+s])))
        ==
      ::
          %spy
        =.  e.s  ?~(h=(~(get by ali.nog) e.s) e.s u.h)
        =.  p.s  ?~(h=(~(get by ali.nog) p.s) p.s u.h)
        :-  s
        %=  nog
          def  (~(put by def.nog) d.s [u |+s])
          use  (~(add ja (~(add ja use.nog) e.s [u |+s])) p.s [u |+s])
        ==
      ::
          %mer
        =.  k.s  ?~(h=(~(get by ali.nog) k.s) k.s u.h)
        =.  u.s  ?~(h=(~(get by ali.nog) u.s) u.s u.h)
        =.  f.s  ?~(h=(~(get by ali.nog) f.s) f.s u.h)
        =.  use.nog  (~(add ja use.nog) k.s [u |+s])
        =.  use.nog  (~(add ja use.nog) u.s [u |+s])
        =.  use.nog  (~(add ja use.nog) f.s [u |+s])
        :-  s
        %=  nog
          def  (~(put by def.nog) d.s [u |+s])
        ==
      ::
          %don
        =.  s.s  ?~(h=(~(get by ali.nog) s.s) s.s u.h)
        [s nog(use (~(add ja use.nog) s.s [u |+s]))]
      ::
          ?(%bom %hip %hop)
        [s nog]
      ==
    --
  --
::    get analysis result by bell
::
++  puck
  |=  b=bell
  =>  [b=b m=moan ..hone]
  ~+
  =/  h  (~(get ja m) form.b)
  |-  ^-  hone
  ?<  ?=(~ h)
  ?:  =(text.b soot.i.h)  i.h
  $(h t.h)
::    compute which analysis results are not linearized and return in
::    toposorted order
::
++  work
  ^-  (list bell)
  =/  mell=(set bell)
    %-  ~(rep by moan)
    |=  [[f=* l=(list hone)] mell=(set bell)]
    (roll l |:([h=*hone mell=mell] (~(put in mell) [soot.h f])))
  =/  novo  (~(dif in mell) `(set bell)`~(key by peal.fuji))
  =/  sire=(jug bell bell)
    %-  ~(rep in novo)
    |=  [b=bell sire=(jug bell bell)]
    =/  hues  (puck b)
    =/  team  (~(gas in *(set bell)) ~(val by ices.norm.hues))
    =.  team  (~(dif in team) loop.norm.hues)
    =.  team  (~(int in team) novo)
    %-  ~(rep in team)
    |:  [k=*bell s=sire]
    (~(put ju s) k b)
  =<  tack.s
  %-  ~(rep in novo)
  |=  [v=bell s=[done=(set bell) tack=(list bell)]]
  =*  dfs  $
  ^-  _s
  ?:  (~(has in done.s) v)  s
  =.  done.s  (~(put in done.s) v)
  =/  e=(set bell)  (~(get ju sire) v)
  :: =.  e  (~(dif in e) done.s)  :: XX restore?
  =.  s
    %-  ~(rep in e)
    |:  [n=*bell s=s]
    ^-  _s
    dfs(v n, s s)
  s(tack [v tack.s])
::
::    internal state
::
::  redo: call-sites without registerization
::  pile: arm under construction
::
+$  gen  [redo=(list [t=bell b=@uwoo]) =pile]
::
++  jean
  |_  [labe=@uxor like=(map bell (pair @uxor need)) =gen]
  ::
  ::    core DDCG linearizer
  ::
  ++  cuts
    =/  =goal  [%done ~]
    |=  =bell
    =.  bell.pile.gen  bell
    =/  h  (puck bell)
    =*  n  nomm.norm.h
    |-  ^-  [next _gen]
    ?-  -.n
        %par
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  loch  gen  (emit ~ ~ %don last)
        $(goal [%next [%this last] loch])
      ::
          %pick  bomb :: XX was +mine
      ::
          %next
        =^  [left=need rite=need bill=@uwoo]  gen  (lyse goal)
        =^  tale  gen
          $(n rite.n, goal [%next rite bill])
        =^  hale  gen
          $(n left.n, goal [%next left then.tale])
        (copy hale what.tale)
      ==
    ::
        %not
      ?:  =(0 here.n)  bomb
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  dear  gen  (emit ~ ~ %don last)
        $(goal [%next [%this last] dear])
      ::
          %pick
        =^  cove  gen  rain
        =^  cozy  gen  (emit ~ ~ %brn cove [zero once]:goal)
        $(goal [%next [%this cove] cozy])
      ::
          %next
        (from here.n goal)
      ==
    ::
        %one
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  rime  gen  (emit ~ [%imm moan.n last]~ %don last)
        [[%next [%none ~] rime] gen]
      ::
          %pick
        ?:  =(0 moan.n)
          [[%next [%none ~] zero.goal] gen]
        ?:  =(1 moan.n)
          [[%next [%none ~] once.goal] gen]
        bomb :: XX was +mine
      ::
          %next
        =^  bill  gen  (mede then.goal moan.n what.goal)
        [[%next [%none ~] bill] gen]
      ==
    ::
        %two
      ?:  ?=(%pick -.goal)
        =^  flip  gen  rain
        =^  bird  gen  (emit ~ ~ %brn flip [zero once]:goal)
        $(goal [%next [%this flip] bird])
      =/  bull  (~(get by ices.norm.h) rail.n)
      ?~  bull
        :: indirect call
        ?-  -.goal
            %done
          =^  s  gen  rain
          =^  f  gen  rain
          =^  tide  gen  (emit ~ ~ %lnt s f)
          =^  corn  gen  $(n corn.n, goal [%next [%this f] tide])
          =^  cost  gen  $(n cost.n, goal [%next [%this s] then.corn])
          (copy cost what.corn)
        ::
            %next
          =^  [post=@uwoo salt=@uvre]  gen  (kerf goal)
          =^  s  gen  rain
          =^  f  gen  rain
          =^  dine  gen  (emit ~ ~ %lnk s f salt post)
          =^  corn  gen  $(n corn.n, goal [%next [%this f] dine])
          =^  cost  gen  $(n cost.n, goal [%next [%this s] then.corn])
          (copy cost what.corn)
        ==
      :: direct call
      =/  hope  (~(get by call.cole) u.bull)
      ::
      ::    when we emit code for a direct call, we hope to know the
      ::    registerization already. If we don't, we need to add the call to
      ::    the redo set. If we do, then we need a linear list of argument
      ::    registers, as well as a need which describes which parts of the
      ::    call subject go in which registers
      ::
      =^  a=[r=? wool=@uxor v=(list @uvre) n=need]  gen
        ?^  wip=(~(get by like) u.bull)
          =^  s  gen  (scar q.u.wip)
          [[| p.u.wip s] gen]
        :: XX only sometimes recur=(~(has in loop.norm.h) u.bull)
        =^  s  gen  rain
        [[& 0x0 ~[s] [%this s]] gen]
      ::
      ?-  -.goal
          %done
        =^  [dire=@uwoo seed=need]  gen
          ?~  hope
            =^  dike  gen  (emit ~ ~ %jmp wool.a v.a)
            =?  redo.gen  r.a  [[u.bull dike] redo.gen]
            [[dike n.a] gen]
          =^  s  gen  rain
          =^  dial  gen  (emit ~ ~ %jmf wool.a v.a s u.hope)
          =?  redo.gen  r.a  [[u.bull dial] redo.gen]
          =^  nest  gen  (copy [%next n.a dial] [%this s])
          [[then.nest what.nest] gen]
        =^  corn  gen  $(n corn.n, goal [%next [%none ~] dire])
        =^  cost  gen  $(n cost.n, goal [%next seed then.corn])
        (copy cost what.corn)
      ::
          %next
        =^  [post=@uwoo salt=@uvre]  gen  (kerf goal)
        =^  [dire=@uwoo seed=need]  gen
          ?~  hope
            =^  dine  gen  (emit ~ ~ %cal wool.a v.a salt post)
            =?  redo.gen  r.a  [[u.bull dine] redo.gen]
            [[dine n.a] gen]
          =^  s  gen  rain
          =^  dime  gen  (emit ~ ~ %caf wool.a v.a salt post s u.hope)
          =?  redo.gen  r.a  [[u.bull dime] redo.gen]
          =^  nest  gen  (copy [%next n.a dime] [%this s])
          [[then.nest what.nest] gen]
        =^  corn  gen  $(n corn.n, goal [%next [%none ~] dire])
        =^  cost  gen  $(n cost.n, goal [%next seed then.corn])
        (copy cost what.corn)
      ==
    ::
        %the
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  hasp  gen  rain
        =^  tear  gen  (emit ~ [%imm 0 last]~ %don last)
        =^  fear  gen  (emit ~ [%imm 1 hasp]~ %don hasp)
        $(goal [%pick tear fear])
      ::
          %next
        ?:  ?=(?(^ %both) -.what.goal)
          ?.  ?=([%both @ %& *] what.goal)  bomb
          (mine r.what.goal then.goal)
        ::  no need for check if result unused
        ?:  ?=(%none -.what.goal)
          $(n pell.n)
        =^  [z=@uwoo o=@uwoo]  gen
          (phin r.what.goal then.goal)
        $(goal [%pick z o])
      ::
          %pick
        =^  coat  gen  rain
        =^  pith  gen  (emit ~ ~ %clq coat [zero once]:goal)
        $(n pell.n, goal [%next [%this coat] pith])
      ==
    ::
        %for
      ?-  -.goal
          %done
        =^  rink  gen  rain
        =^  pink  gen  rain
        =^  tike  gen  (emit ~ [%inc pink rink]~ %don rink)
        $(n mall.n, goal [%next [%this pink] tike])
      ::
          %pick
        =^  rink  gen  rain
        =^  pink  gen  rain
        =^  pike  gen
          (emit ~ [%inc pink rink]~ %brn rink [zero once]:goal)
        $(n mall.n, goal [%next [%this pink] pike])
      ::
          %next
        ?:  ?=(?(^ %both) -.what.goal)
          ?.  ?=([%both @ %& *] what.goal)  bomb
          (mine r.what.goal then.goal)
        =^  rink  gen
          ?:  ?=(%none -.what.goal)
            rain
          [r.what.goal gen]
        =^  pink  gen  rain
        =^  bike  gen  (emit ~ [%inc pink rink]~ %hop then.goal)
        $(n mall.n, goal [%next [%this pink] bike])
      ==
    ::
        %ivy
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  hasp  gen  rain
        =^  reek  gen  (emit ~ [%imm 0 last]~ %don last)
        =^  riff  gen  (emit ~ [%imm 1 hasp]~ %don hasp)
        $(goal [%pick reek riff])
      ::
          %next
        ?:  ?=(?(^ %both) -.what.goal)
          ?.  ?=([%both @ %& *] what.goal)  bomb
          (mine r.what.goal then.goal)
        ?:  ?=(%none -.what.goal)
          =^  than  gen  $(n that.n)
          =^  thin  gen  $(n this.n, then.goal then.than)
          (copy thin what.than)
        =^  [z=@uwoo o=@uwoo]  gen
          (phin r.what.goal then.goal)
        $(goal [%pick z o])
      ::
          %pick
        =^  tire  gen  rain
        =^  tear  gen  rain
        =^  pare  gen  (emit ~ ~ %eqq tire tear [zero once]:goal)
        =^  than  gen  $(n that.n, goal [%next [%this tear] pare])
        =^  thin  gen  $(n this.n, goal [%next [%this tire] then.than])
        (copy thin what.than)
      ==
    ::
        %six
      ?:  ?=(%next -.goal)
        =^  [teal=next feel=next]  gen  (phil goal)
        =^  fest  gen  $(n else.n, goal feel)
        =^  zest  gen  $(n then.n, goal teal)
        =^  [bead=need tile=@uwoo file=@uwoo]  gen  (sect zest fest)
        =^  cond  gen  $(n what.n, goal [%pick tile file])
        (copy cond bead)
      =^  fest  gen  $(n else.n)
      =^  zest  gen  $(n then.n)
      =^  [bead=need tile=@uwoo file=@uwoo]  gen  (sect zest fest)
      =^  cond  gen  $(n what.n, goal [%pick tile file])
      (copy cond bead)
    ::
        %eve
      =^  thin  gen  $(n then.n)
      $(n once.n, goal thin)
    ::
        %ten
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  dead  gen  (emit ~ ~ %don last)
        $(goal [%next [%this last] dead])
      ::
          %pick
        ?.  =(here.n 1)  bomb :: XX was +mine
        =^  flip  gen  rain
        =^  deep  gen  (emit ~ ~ %brn flip [zero once]:goal)
        $(goal [%next [%this flip] deep])
      ::
          %next
        =^  [twig=need tree=need then=@uwoo]  gen  (into here.n goal)
        =^  nest  gen  $(n tree.n, goal [%next tree then])
        =^  eggs  gen  $(n twig.n, goal [%next twig then.nest])
        (copy eggs what.nest)
      ==
    ::
        %sip
      ?+  hint.n  $(n then.n)
          %bout
        ?-  -.goal
            %done
          =^  last  gen  rain
          =^  dime  gen  (emit ~ ~ %don last)
          $(goal [%next [%this last] dime])
        ::
            %pick
          =^  tome  gen  (emit ~ [%tom ~]~ %hop zero.goal)
          =^  foam  gen  (emit ~ [%tom ~]~ %hop once.goal)
          =^  race  gen  $(n then.n, goal [%pick tome foam])
          =^  tick  gen  (emit ~ [%tim ~]~ %hop then.race)
          [race(then tick) gen]
        ::
            %next
          =^  stop  gen  (emit ~ [%tom ~]~ %hop then.goal)
          =^  race  gen  $(n then.n, then.goal stop)
          =^  goes  gen  (emit ~ [%tim ~]~ %hop then.race)
          [race(then goes) gen]
        ==
      ::
          %meme
        =^  raft  gen  $(n then.n)
        =^  meme  gen  (emit ~ [%mem ~]~ %hop then.raft)
        [raft(then meme) gen]
      ==
    ::
        %tip
      ?+    hint.n
        =^  thin  gen  $(n then.n)
        =^  fake  gen  $(n vice.n, goal [%next [%none ~] then.thin])
        (copy fake what.thin)
      ::
          ?(%hunk %hand %lose %mean %spot)
        =^  real  gen
          |-  ^-  [next _gen]
          ?-  -.goal
              %done  ^$(n then.n)  :: NB implicit %man
              %pick
            =^  mere  gen  rain
            =^  chit  gen  (emit ~ ~ %brn mere zero.goal once.goal)
            $(goal [%next [%this mere] chit])
          ::
              %next
            =^  rugs  gen  (emit ~ [%man ~]~ %hop then.goal)
            ^$(n then.n, then.goal rugs)
          ==
        =^  [body=(list pole) ned=need]  gen  (aver what.real)
        =^  mane  gen  rain
        =^  dint  gen  (emit ~ [[%men hint.n mane] body] %hop then.real)
        =^  fake  gen  $(n vice.n, goal [%next [%this mane] dint])
        (copy fake ned)
      ::
          ?(%live %slog)
        =^  clue  gen  rain
        =^  real  gen  $(n then.n)
        =/  pol   ?:(?=(%live hint.n) [%hit clue] [%slg clue])
        =^  wave  gen  (emit ~ [pol]~ %hop then.real)
        =^  fake  gen  $(n vice.n, goal [%next [%this clue] wave])
        (copy fake what.real)
      ::
          %memo
        =>  =*  dot  .
            ?.  ?=(%done -.goal)  dot
            =^  salt  gen  rain
            =^  mode  gen  (emit ~ ~ %don salt)
            dot(goal [%next [%this salt] mode])
        =^  funk  gen  rain
        =^  gunk  gen  rain
        =^  sunk  gen  rain
        =^  [ned=need =site]  gen
          ?-  -.goal
              %pick
            =^  mere  gen  rain
            =^  chit  gen  (emit ~ ~ %brn mere zero.goal once.goal)
            =^  loot  gen  rain
            =^  root  gen  rain
            =^  loam  gen  (emit ~ ~[[%imm 0 loot] [%mew gunk sunk funk loot]] %hop zero.goal)
            =^  rome  gen  (emit ~ ~[[%imm 1 root] [%mew gunk sunk funk root]] %hop once.goal)
            =^  moog  gen  $(n then.n, zero.goal loam, once.goal rome)
            [[what.moog [%mer gunk sunk funk mere chit then.moog]] gen]
          ::
              %next
            =^  [chit=next miss=next]    gen  (phil goal)
            =^  [chin=@uwoo mere=@uvre]  gen  (kerf chit)
            =^  [misc=@uwoo salt=@uvre]  gen  (kerf miss)
            =^  meow  gen  (emit ~ [%mew gunk sunk funk salt]~ %hop misc)
            =^  real  gen  $(n then.n, goal [%next [%this salt] meow])
            [[what.real [%mer gunk sunk funk mere chin then.real]] gen]
          ==
        =/  body=(list pole)
          ~[[%imm 0 gunk] [%imm (~(got by fizz.norm.h) hare.n) funk]]
        =^  cake  gen  (emit ~ body site)
        =^  fake  gen  $(n vice.n, goal [%next [%none ~] cake])
        =^  cope  gen  (copy fake ned)
        (copy cope [%this sunk])
      ::
          :: %bout  ~|  %todo  !!
      ==
    ::
        %elf
      =>  =*  dot  .
          ?:  ?=(%next -.goal)  dot
          =^  reg  gen  rain
          =/  sit  ?:(?=(%done -.goal) [%don reg] [%brn reg |1.goal])
          =^  uwo  gen  (emit ~ ~ sit)
          dot(goal [%next [%this reg] uwo])
      =^  [weft=@uwoo good=@uvre]  gen  (kerf goal)
      =^  home  gen  rain
      =^  path  gen  rain
      =^  show  gen  (emit ~ ~ %spy home path good weft)
      =^  trot  gen  $(n walk.n, goal [%next [%this path] show])
      =^  paid  gen  $(n rent.n, goal [%next [%this home] then.trot])
      (copy paid what.trot)
    ==
  ::
  ::    redo callsite registerization
  ::
  ::  given recursion, we may not know the registerization for an arm
  ::  when we generate a direct call to it. Thus, once we have generated
  ::  code for all arms in the call tree and know their
  ::  registerizations, we return to callsites and generate
  ::  properly-registerized calls, without changing the registerization
  ::  of the calling arm.
  ++  redo
    |=  [=bell u=@uwoo]
    ^-  _gen
    =/  [wool=@uxor n=need]
      ~|  =/  h  ~|(%puck-bell (puck bell.pile.gen))
          ((outa:blot:sack "redo fail: " `@`0 [seat area]:norm.h) %redo-fail)
      (~(got by like) bell)  :: XX
    =/  blob  (~(got by will.pile.gen) u)
    ::
    =^  urge=[v=(list @uvre) n=need]  gen  (scar n)
    ::
    :: ?.  =((lent walt.urge) (lent v.urge))
    ::       ~|  %bad-shit2  !!
    ::
    ?+  -.bend.blob  ~|  %redo-cant  !!
        %cal
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ::
        %caf
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ::
        %jmp
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ::
        %jmf
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ==
  ::  +kerf: split single register into goal
  ::
  ::    given a destination, generate code which splits a noun in one
  ::    register to the registers described by the $need, and return the
  ::    one register and a label for the splitting code
  ::
  ++  kerf
    |=  nex=next
    ^-  [[@uwoo @uvre] _gen]
    =^  [r=@uvre p=(list pole)]  gen  (kern ~ what.nex)
    ?~  p  [[then.nex r] gen]
    =^  u  gen  (emit ~ p %hop then.nex)
    [[u r] gen]
  ::  +kern: split register to need (instruction list)
  ::
  ::    like +kerf but return (reversed) instruction list
  ::    instead of emitting basic block
  ::
  ++  kern
    |=  [p=(list pole) ned=need]
    ^-  [[@uvre (list pole)] _gen]
    =;  [[r=(unit @uvre) l=(list pole)] =_gen]
      ?^  r  [[u.r l] gen]
      ?>  ?=(~ l)
      =^(r gen rain [[r ~] gen])
    |-  ^-  [(pair (unit @uvre) (list pole)) _gen]
    ?-    -.ned
        ^
      =^  r  gen  rain
      $(ned [%both r | ned])
    ::
        %both
      =^  r  gen  $(ned t.ned)
      =^  l  gen  $(ned h.ned, p ?~(p.r q.r [[%tal r.ned u.p.r] q.r]))
      =-  [[`r.ned ?:(c.ned - [[%cel r.ned] -])] gen]
      ?~(p.l q.l [[%hed r.ned u.p.l] q.l])
    ::
        %this  [[`r.ned p] gen]
        %none  [`p gen]
    ==
  ::
  ++  emit                                              ::  add block
    |=  =blob
    ^-  [@uwoo _gen]
    =^(l gen vial [l (emir l blob)])
  ::
  ++  emir                                              ::  put block
    |=  [l=@uwoo =blob]
    ^+  gen
    gen(will.pile (~(put by will.pile.gen) l blob))
  ::
  ++  rain                                              ::  new register
    ^-  [@uvre _gen]
    [sans.pile.gen gen(sans.pile .+(sans.pile.gen))]
  ::
  ++  aver
    |=  ned=need
    =|  p=(list pole)
    |-  ^-  [(pair (list pole) need) _gen]
    ?+    -.ned
      [[p ned] gen]
    ::
        ^
      =^  q  gen  $(ned q.ned)
      =^  p  gen  $(ned p.ned, p p.q)
      =^  r  gen  rain
      [[[[%cel r] p.p] [%both r & q.p q.q]] gen]
    ::
        %both
      ?:  c.ned
        [[p ned] gen]
      =^  q  gen  $(ned t.ned)
      =^  p  gen  $(ned h.ned, p p.q)
      [[[[%cel r.ned] p.p] ned(c &, h q.p, t q.q)] gen]
    ==
  ::
  ++  must
    |=  ned=need
    ^-  [(pair @uvre $>(?(%both %this) need)) _gen]
    ?-  -.ned
      ^      =^(r gen rain [[r %both r | ned] gen])
      %both  [[r.ned ned] gen]
      %this  [[r.ned ned] gen]
      %none  =^(r gen rain [[r %this r] gen])
    ==
  ::  +lyse: split need for cons
  ::
  ++  lyse
    |=  nex=next
    ^-  [[need need @uwoo] _gen]
    =*  ned  what.nex
    ?-    -.ned
        ^      [[p.ned q.ned then.nex] gen]
    ::
        %both
      =^  l  gen  (must h.ned)
      =^  r  gen  (must t.ned)
      =^  u  gen  (emit ~ [%con p.l p.r r.ned]~ %hop then.nex)
      [[q.l q.r u] gen]
    ::
        %this
      =^  l  gen  rain
      =^  r  gen  rain
      =^  u  gen  (emit ~ [%con l r r.ned]~ %hop then.nex)
      [[[%this l] [%this r] u] gen]
    ::
        %none  [[ned ned then.nex] gen]
    ==
  ::  +sect: align subject needs for branching computation
  ::
  ::    this generates the maximally common split of registers between
  ::    both branches. If one branch expects a cell at an axis but the other does
  ::    not, then we must expect that axis in a register so we do not
  ::    crash when the more permissive branch would be taken
  ::
  ++  sect
    |=  [zero=next once=next]
    ^-  [[need @uwoo @uwoo] _gen]
    =|  lp=(list (list pole))
    =|  rp=(list (list pole))
    =|  s=(list need)
    =/  t=(list (each (unit [r=@uvre c=?]) [z=need o=need]))
      [%| what.zero what.once]~
    |-  ^-  [[need @uwoo @uwoo] _gen]
    ?~  t
      ?>  ?=([^ ~] s)
      =^  lu  gen  (emit ~ (zing (flop lp)) %hop then.zero)
      =^  ru  gen  (emit ~ (zing (flop rp)) %hop then.once)
      [[i.s lu ru] gen]
    ?:  ?=(%& -.i.t)
      ?>  ?=([^ ^] s)
      =/  par  [i.t.s i.s]
      $(t t.t, s [?~(p.i.t par [%both r.u.p.i.t c.u.p.i.t par]) t.t.s])
    =*  z  z.p.i.t
    =*  o  o.p.i.t
    ?:  ?=(?(%none %this) -.z)
      ?:  ?=(%none -.o)
        $(t t.t, s [z s])
      =^  rr=[r=@uvre p=(list pole)]  gen  (kern ~ o)
      =?  lp  ?=(%this -.z)
         [[%mov r.rr r.z]~ lp]
      $(rp [p.rr rp], t t.t, s [[%this r.rr] s])
    ::
    ?:  ?=(?(%none %this) -.o)
      =^  lr=[r=@uvre p=(list pole)]  gen  (kern ~ z)
      =?  rp  ?=(%this -.o)
         [[%mov r.lr r.o]~ rp]
      $(lp [p.lr lp], t t.t, s [[%this r.lr] s])
    ::
    ?^  -.z
      ?^  -.o
        $(t [[%| p.z p.o] [%| q.z q.o] [%& ~] t.t])
      $(t [[%| p.z h.o] [%| q.z t.o] [%& `[r.o |]] t.t])
    ::
    ?^  -.o
      $(t [[%| h.z p.o] [%| t.z q.o] [%& `[r.z |]] t.t])
    %=  $
      t   [[%| h.z h.o] [%| t.z t.o] [%& `[r.z &(c.z c.o)]] t.t]
      rp  [[%mov r.z r.o]~ rp]
    ==
  ::  +copy: align subject needs for sequential computation
  ::
  ::    generate a need split as far as either input need is split,
  ::    generating cons code for less-split need. This is used when two
  ::    sequential subformulas read from the same subject
  ::
  ::    for correctness in crash handling it is vital that the needs are
  ::    ordered by the evaluation order of the computations, so that the
  ::    first need is from the first computation and the second need from
  ::    the second.
  ::
  ++  copy
    |=  [feed=next seed=need]
    ^-  [next _gen]
    =|  p=(list pole)
    =|  s=(list need)
    =/  t=(list (each (unit [r=@uvre c=?]) [l=need r=need]))
      [%| what.feed seed]~
    |-  ^-  [next _gen]
    ?~  t
      ?>  ?=([^ ~] s)
      =^  u  gen  (emit ~ p %hop then.feed)
      [[%next i.s u] gen]
    ?:  ?=(%& -.i.t)
      ?>  ?=([^ ^] s)
      =/  par  [i.t.s i.s]
      $(t t.t, s [?~(p.i.t par [%both r.u.p.i.t c.u.p.i.t par]) t.t.s])
    =*  l  l.p.i.t
    =*  r  r.p.i.t
    ?:  ?=(%none -.l)  $(s [r s], t t.t)
    ?:  ?=(%none -.r)  $(s [l s], t t.t)
    ::
    ?:  ?=(%this -.l)
      ?:  ?=(%this -.r)
        ~?  =(r.l r.r)  [%copy-this-l-a r.l r.r]  :: XX strange
        $(p [[%mov r.l r.r] p], s [l s], t t.t)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen rain [[%both x | r] gen]))
      ~?  =(r.l r.rr)  [%copy-this-l-b r.l r.rr]  :: XX strange
      $(p [[%mov r.rr r.l] p], s [rr s], t t.t)
    ::
    ?:  ?=(%this -.r)
      =^  ll=$>(%both need)  gen
        ?@(-.l [l gen] =^(x gen rain [[%both x | l] gen]))
      ~?  =(r.ll r.r)  [%copy-this-r r.ll r.r]  :: XX strange
      $(p [[%mov r.ll r.r] p], s [ll s], t t.t)
    ::
    ?:  ?=(%both -.l)
      =^  rr=$>(%both need)  gen
        ?@(-.r [r gen] =^(x gen rain [[%both x | r] gen]))
      ~?  =(r.l r.rr)  [%copy-both r.l r.rr]  :: XX strange
      %=  $
        p  [[%mov r.rr r.l] p]
        t  [[%| h.l h.rr] [%| t.l t.rr] [%& `[r.rr &(c.l c.rr)]] t.t]
      ==
    ::  ?=(%both -.r)
    ::
    ?^  -.r
      $(t [[%| p.l p.r] [%| q.l q.r] [%& ~] t.t])
    $(t [[%| p.l h.r] [%| q.l t.r] [%& `[r.r |]] t.t])
  ::
  ++  bomb                                              ::  crash
    ^-  [next _gen]
    =^  b  gen  (emit ~ ~ %bom ~)
    [[%next [%none ~] b] gen]
  ::  +mine: set up deferred crash
  ::
  ++  mine
    |=  [r=@uvre t=@uwoo]
    ^-  [next _gen]
    ::  NB: store 0 so that a subsequent %cel check will crash
    =^  mile  gen  (emit ~ [%imm 0 r]~ %hop t)
    [[%next [%none ~] mile] gen]
  ::
  ++  vial                                              ::  new label
    ^-  [@uwoo _gen]
    [well.pile.gen gen(well.pile +(well.pile.gen))]
  ::
  ++  come                                              ::  label come-from
    |=  [f=@uwoo t=@uwoo]
    ^+  gen
    (emir f [~ ~ %hip f t])
  ::  +phil: generate phi nodes
  ::
  ::    given a destination common to two branches, generate a phi node
  ::    and come-from blocks
  ::
  ++  phil
    |=  nex=next
    ^-  [[next next] _gen]
    =/  t=(list (each (unit [c=? z=@uvre o=@uvre]) need))  [%| what.nex]~
    =|  s=(list [z=need o=need])
    =|  b=(map @uvre (map @uwoo @uvre))
    =^  zb  gen  vial
    =^  ob  gen  vial
    |-  ^-  [[next next] _gen]
    ?~  t
      ?>  ?=([^ ~] s)
      =^  f  gen  (emit b ~ %hop then.nex)
      =.  gen  (come zb f)
      =.  gen  (come ob f)
      [[[%next z.i.s zb] [%next o.i.s ob]] gen]
    ::
    ?:  ?=(%& -.i.t)
      ?>  ?=([^ ^] s)
      =+  ^=  [z o]
        ?~  p.i.t
          [[z.i.t.s z.i.s] o.i.t.s o.i.s]
        :*  [%both z.u.p.i.t c.u.p.i.t z.i.t.s z.i.s]
            [%both o.u.p.i.t c.u.p.i.t o.i.t.s o.i.s]
        ==
      $(t t.t, s [[z o] t.t.s])
    ::
    =*  p  p.i.t
    ?:  ?=(%none -.p)
      $(s [[p p] s], t t.t)
    ?^  -.p
      $(t [[%| p.p] [%| q.p] [%& ~] t.t])
    ::
    =^  l  gen  rain
    =^  r  gen  rain
    =/  fib  (~(gas by *(map @uwoo @uvre)) ~[[zb l] [ob r]])
    ?-  -.p
      %this  %=  $
               b  (~(put by b) r.p fib)
               s  [[[%this l] %this r] s]
               t  t.t
             ==
    ::
      %both  %=  $
               b  (~(put by b) r.p fib)
               t  [[%| h.p] [%| t.p] [%& `[c.p l r]] t.t]
    ==       ==
  ::  +phin: +phil for loobean-product opcodes
  ::
  ++  phin
    |=  [reg=@uvre ten=@uwoo]  ::  [%next [%this reg] ten]
    ^-  [(pair @uwoo @uwoo) _gen]
    =^  tare  gen  rain
    =^  tile  gen  vial
    =^  fare  gen  rain
    =^  file  gen  vial
    =^  thin  gen
      =-  (emit - ~ %hop ten)
      %+  ~(put by *(map @uvre (map @uwoo @uvre)))  reg
      (~(gas by *(map @uwoo @uvre)) ~[[tile tare] [file fare]])
    =.  gen  (come tile thin)
    =.  gen  (come file thin)
    =^  celt  gen  (emit ~ [%imm 0 tare]~ %hop tile)
    =^  felt  gen  (emit ~ [%imm 1 fare]~ %hop file)
    [[celt felt] gen]
  ::  +scar: generate fresh parameter lists
  ::
  ::    generate fresh parameter variables and provide them both in
  ::    argument list and need form
  ::
  ++  scar
    |=  n=need
    =|  rv=(list @uvre)
    =/  t=(list (each (unit [r=@uvre c=?]) need))  [%| n]~
    =|  s=(list need)
    |-  ^-  [[v=(list @uvre) n=need] _gen]
    ?~  t
      ?>  ?=([^ ~] s)
      [[(flop rv) i.s] gen]
    ?:  ?=(%& -.i.t)
      ?>  ?=([^ ^] s)
      =/  par  [i.t.s i.s]
      $(t t.t, s [?~(p.i.t par [%both r.u.p.i.t c.u.p.i.t par]) t.t.s])
    ::
    =*  p  p.i.t
    ?:  ?=(%none -.p)
      $(t t.t, s [p s])
    ?^  -.p
      $(t [[%| p.p] [%| q.p] [%& ~] t.t])
    =^  vr  gen  rain
    ?-  -.p
      %both  $(t [[%| h.p] [%| t.p] [%& `[vr c.p]] t.t])
      %this  $(t t.t, s [[%this vr] s], rv [vr rv])
    ==
  ::  +from: push need down by axis
  ::
  ++  from
    |=  [axe=@ nex=next]
    ^-  [next _gen]  :: XX return need
    ?<  =(0 axe)
    =-  [[%next - then.nex] gen]
    =*  ned  what.nex
    |-  ^-  need
    ?:  =(1 axe)  ned
    =/  lat  (mas axe)
    ?-  (cap axe)
      %2  [$(axe lat) [%none ~]]
      %3  [[%none ~] $(axe lat)]
    ==
  ::  +into: split need for edit
  ::
  ::    first returned need is for the patch noun,
  ::    the second is for the noun to be edited
  ::
  ++  into
    |=  [axe=@ nex=next]
    ^-  [[need need @uwoo] _gen]
    ?<  =(0 axe)
    ?:  =(1 axe)
      [[what.nex [%none ~] then.nex] gen]
    =|  s=(list [h=? n=need])
    =|  p=(list pole)
    =*  ned  what.nex
    |-  ^-  [[need need @uwoo] _gen]
    ?:  =(1 axe)
      :: XX ?~(p [then.nex gen] (emit ...))
      =^  u  gen  (emit ~ p %hop then.nex)
      ::  NB: depends on =(%none -:*need)
      =/  big  (roll s |=([[h=? n=need] t=need] ?:(h [t n] [n t])))
      [[ned big u] gen]
    ::
    =+  [h lat]=[?=(%2 (cap axe)) (mas axe)]
    ?-    -.ned
        ^
      =+  [a b]=?:(h ned [q.ned p.ned])
      $(s [[h b] s], ned a, axe lat)
    ::
        %both
      =^  l  gen  (must h.ned)
      =^  r  gen  (must t.ned)
      =/  =pole  [%con p.l p.r r.ned]
      =+  [a b]=?:(h [q.l q.r] [q.r q.l])
      $(s [[h b] s], ned a, p [pole p], axe lat)
    ::
        %this
      =^  l  gen  rain
      =^  r  gen  rain
      =/  =pole  [%con l r r.ned]
      =+  [a b]=?:(h [l r] [r l])
      $(s [[h %this b] s], ned [%this a], p [pole p], axe lat)
    ::
        %none  $(s [[h ned] s], axe lat)
    ==
  ::  +mede: split immediate into registers of need
  ::
  ++  mede
    |=  [u=@uwoo n=* ned=need]
    ^-  [@uwoo _gen]
    =|  p=(list pole)
    =/  s=(list [non=* ned=need])  [n ned]~
    |-  ^-  [@uwoo _gen]
    ?~  s  (emit ~ p %hop u)
    =*  ne  ned.i.s
    =*  no  non.i.s
    ?-    -.ne
        ^
      ?^  no
        $(s [[+.no q.ne] [-.no p.ne] t.s])
      =^  r  gen  rain
      $(i.s i.s(ned [%both r | ne]))
    ::
        %both
      ?.  |(c.ne ?=(^ no))
        =^  y  gen  (emit ~ ~ %bom ~)
        $(u y, s t.s)
      =^  [y=@uwoo r=@uvre]  gen  (kerf [%next ne u])
      $(p [[%imm ?^(no no 0) r] p], u y, s t.s) :: NB %cel crash
    ::
        %this  $(p [[%imm no r.ne] p], s t.s)
        %none  $(s t.s)
    ==
  ::  +bede: balance need and emit %cons (reversed)
  ::
  ++  bede
    |=  n=need
    ^-  [(pair (list pole) need) _gen]
    ?:  =(%none -.n)  [[~ n] gen]
    =|  out=(list pole)
    |-  ^-  [(pair (list pole) $>(?(%both %this) need)) _gen]
    =^  [@uvre den=$>(?(%both %this) need)]  gen  (must n)
    ?.  ?=(%both -.den)
      [[out den] gen]
    =^  r  gen  $(n t.den)
    =^  l  gen  $(n h.den, out p.r)
    =/  lr  ?:(?=(%this -.q.l) r.q.l r.q.l)
    =/  rr  ?:(?=(%this -.q.r) r.q.r r.q.r)
    [[[[%con lr rr r.den] p.l] den(h q.l, t q.r)] gen]
  --
::  +sede: restrict need by sock
::
++  sede
  |=  [n=need s=sock out=(list pole)]
  ^-  (pair (list pole) need)
  [out n] :: XX
::  +sill: list of registers from a need
::
++  sill
  |=  want=need
  =|  wart=(list @uvre)
  =/  tack=(list need)  ~[want]
  |-  ^-  (list @uvre)
  ?~  tack  wart
  ?-  -.i.tack
    ^      $(tack [q.i.tack p.i.tack t.tack])
    %this  $(wart [r.i.tack wart], tack t.tack)
    %both  $(tack [t.i.tack h.i.tack t.tack])
    %none  $(tack t.tack)
  ==
::  +mill: loop over redos
::
::    run redo:jean on each arm in the redo list, which will generate
::    code to properly registerize callsites whose registerization was
::    deferred, without changing the registerization of the calling arm
::
++  mill
  =|  todo=(list [labe=@uxor dire=next =gen])
  =/  like  peal.fuji
  =/  toil  work
  =/  band  |2.fuji
  |-  ^+  fuji
  ?^  toil
    =^  labe  band
      ?^  free.band
        [i.free.band band(free t.free.band)]
      [next.band band(next +(next.band))]
    =/  [dire=next =gen]  (~(cuts jean [labe like *gen]) i.toil)
    ::
    ::  reserved entrypoints
    ::
    =.  gen
      =^  [wish=@uwoo sire=@uvre]  gen  (~(kerf jean [labe like gen]) dire)
      (~(emir jean [labe like gen]) 0w0 [~ [%mov 0v0 sire]~ %hop wish])
    =>  =*  dot  .
        =^  [con=(list pole) ned=need]  gen
          (~(bede jean [labe like gen]) what.dire)
        =^  lit=(list pole)  what.dire
          (sede ned text.i.toil (flop con))
        ~?  ?=(%none -.what.dire)  [%need-none labe]
        %=  dot
          what.dire  what.dire
          gen  (~(emir jean [labe like gen]) 0w1 [~ lit %hop then.dire])
        ==
    ::
    =.  like  (~(put by like) i.toil [labe what.dire])
    ?^  redo.gen
      $(toil t.toil, todo [[labe dire gen] todo])
    %=    $
        toil  t.toil
        hill.fuji
      %+  ~(put by hill.fuji)  labe
      ~(bake py pile.gen(walt (sill what.dire)))
    ==
  |-  ^+  fuji
  ?^  todo
    =*  gen  gen.i.todo
    =.  gen
      %+  roll  redo.gen
      |=([[b=bell u=@uwoo] =_gen] (~(redo jean [labe.i.todo like gen]) b u))
    %=    $
        todo  t.todo
        hill.fuji
      %+  ~(put by hill.fuji)  labe.i.todo
      ~(bake py pile.gen(walt (sill what.dire.i.todo)))
    ==
  ::
  fuji(peal like, |2 band)
--
=+  ver=%1
|%
++  this  .
::
++  peek
   |=  [s=* f=*]
    =/  moat  (~(get ja moan) f)
    |-  ^-  (unit (pair @uxor ^fuji))
    ?~  moat  ~
    ?.  (~(huge so:sack soot.i.moat) [& s])
      $(moat t.moat)
    ~|  %not-in-gong
    `[p:(~(got by peal.fuji) [soot.i.moat f]) fuji]
::
++  poke
  |=  =gist
  ~>  %bout
  ^-  [new=(set bell) old=(set bell) =_this]  :: XX fix product type
  ?-    -.gist
  ::
  ::  analyze
  ::
      %comp
    =.  sack
      ~>  %bout.[0 %sack]
      (rout:sack s.gist f.gist)
    ?<  =(~ moan)
    ::  save old codegen table keys
    :: =/  hole  ~(key by peal.fuji)
    ::  codegen
    =.  fuji  mill
    :: =/  heck  ~(key by peal.fuji)
    :: [(~(dif in heck) hole) (~(dif in hole) heck) this]
    [~ ~ this]
  ==
::
++  xray  ~|  %todo  !!
::
++  back
  =>  |%
      ++  r  |=(r=@uvre `tape`['r' '_' (scow %uv r)])
      ++  l  |=(l=@uwoo `tape`['l' '_' (scow %uv l)])
      ++  f  |=(f=@uxor `tape`['f' '_' (scow %ux f)])
      ++  n
        |=  n=need
        =|  out=tape
        |-  ^+  out
        ?-  -.n
            ^      =/  l=(lest need)
                      |-  ^-  (lest need)
                      ?.  ?=(^ -.q.n)
                        [p.n q.n ~]
                      [p.n $(n q.n)]
                   ['[' $(n i.l, out (reel t.l |=([n=need out=_[']' out]] [' ' ^$(n n, out out)])))]
            %this  (weld (r r.n) out)
            %none  ['~' out]
            %both  =/  l=(lest need)  :: XX {r.n}=[...]
                      |-  ^-  (lest need)
                      ?.  ?=(%both -.t.n)
                        [h.n t.n ~]
                      [h.n $(n t.n)]
                   ['[' $(n i.l, out (reel t.l |=([n=need out=_[']' out]] [' ' ^$(n n, out out)])))]
        ==
      ++  sym  |=(s=@ta `tape`['%' (trip s)]) :: XX
      ++  c-args
        |=  v=(list @uvre)
        `tape`(zing (join ", " (turn v r)))
      ++  d-args
        |=  v=(list @uvre)
        `tape`(zing (join ", " (turn v |=(i=@uvre (weld "NOUN_DECL " (r i))))))
      ++  c-pole
        |=  p=pole
        ^-  tape
        ?-    -.p
            %imm
          %+  weld  "NOUN_DECL {(r d.p)} = "
          ?-  n.p
            ^   "CELL_BYTES(\{ mug: {(scow %x (mug n.p))} }); // XX lit"
            %0  "NUL;"
            %1  "ONE;"
            @   =/  wid  (met 5 n.p)
                ?-  wid
                  %1  (zing "ATOM32(" (scow %x n.p) "U);" ~)
                  %2  (zing "ATOM64(" (scow %x n.p) "ULL);" ~)
                  @   "ATOM_BYTES(\{ mug: {(scow %x (mug n.p))} }); // XX lit"
          ==    ==
        ::
          %mov  "NOUN_DECL {(r d.p)} = {(r s.p)};"
          %inc  "NOUN_DECL {(r d.p)} = BUMP({(r s.p)});"
          %con  "NOUN_DECL {(r d.p)} = CONS({(r h.p)}, {(r t.p)});"
          %hed  "NOUN_DECL {(r d.p)} = HEAD({(r s.p)});"
          %tal  "NOUN_DECL {(r d.p)} = TAIL({(r s.p)});"
          %cel  "ASSERT(IS_CELL({(r p.p)}));"
          %men  "MEAN_PUSH(SYMBOL({(sym l.p)}), {(r s.p)});"
          %man  "MEAN_POP();"
          %slo  "SLOW_PUSH({(r s.p)});"
          %sld  "SLOW_POP();"
          %hit  "PROF_HIT({(r s.p)});"
          %slg  "SLOG({(r s.p)});"
          %mew  "MEMO_PUT({(r k.p)}, {(r u.p)}, {(r f.p)}, {(r r.p)});"
          %tim  "BOUT_START();"
          %tom  "BOUT_STOP();"
          %mem  "MEME_SLOG();"
        ==
      ++  c-site
        |=  s=site
        ^-  [[(unit @uxor) (pair (unit @uwoo) (unit @uwoo))] wall]
        ?-  -.s
          %clq  :~  `[`z.s `o.s]
                    "if ( IS_CELL({(r s.s)}) ) goto {(l z.s)};"
                    "else goto {(l o.s)};"
                ==
          %eqq  :~  `[`z.s `o.s]
                    "if ( IS_EQUAL({(r l.s)}, {(r r.s)}) ) goto {(l z.s)};"
                    "else goto {(l o.s)};"
                ==
          %brn  :~  `[`z.s `o.s]
                    "switch ( {(r s.s)} ) \{"
                    "  case 0: goto {(l z.s)};"
                    "  case 1: goto {(l o.s)};"
                    "  default: BAIL();"
                    "}"
                ==
          %hop  [`[`t.s ~] "goto {(l t.s)};" ~]
          %hip  ~|(%strange-hip !!)
          %lnk  :~  `[`t.s ~]
                    "NOUN_DECL {(r d.s)} = NOCK({(r u.s)}, {(r f.s)});"
                    "goto {(l t.s)};"
                ==
          %cal  :~  [`a.s `t.s ~]
                    "NOUN_DECL {(r d.s)} = {(f a.s)}({(c-args v.s)});"
                    "goto {(l t.s)};"
                ==
          %caf  :~  [`a.s `t.s ~]
                    "// jet: {(spud -.n.s)} +{(scow %ud +.n.s)}"
                    "NOUN_DECL {(r d.s)} = {(f a.s)}({(c-args v.s)});"
                    "goto {(l t.s)};"
                ==
          %lnt  [`[~ ~] "return NOCK({(r u.s)}, {(r f.s)});" ~]
          %jmp  [[`a.s ~ ~] "return {(f a.s)}({(c-args v.s)});" ~]
          %jmf  :~  [`a.s ~ ~]
                    "// jet: {(spud -.n.s)} +{(scow %ud +.n.s)}"
                    "return {(f a.s)}({(c-args v.s)});"
                ==
          %spy  :~  `[`t.s ~]
                    "NOUN_DECL {(r d.s)} = SCRY({(r e.s)}, {(r p.s)});"
                    "goto {(l t.s)};"
                ==
          %mer  :~  `[`i.s `m.s]
                    "MEMO_DECL {(r d.s)} = CHECK_MEMO({(r k.s)}, {(r u.s)}, {(r f.s)});"
                    "if ( IS_MEMO({(r d.s)}) ) goto {(l i.s)};"
                    "else goto {(l m.s)};"
                ==
          %don  [`[~ ~] "return {(r s.s)};" ~]
          %bom  [`[~ ~] "BAIL();" ~]
        ==
      ++  c-blob
        |=  [u=@uwoo b=blob]
        ^-  [(unit @uxor) (pair (unit @uwoo) (unit @uwoo)) wain]
        =|  w=wain
        =/  [[ux=(unit @uxor) uw=(pair (unit @uwoo) (unit @uwoo))] wa=wall]
          (c-site bend.b)
        =.  w  (weld (turn wa |=(t=tape (crip [' ' ' ' t]))) w)
        =.  w  (reel body.b |=([p=pole =_w] [(crip [' ' ' ' (c-pole p)]) w]))
        [ux uw ['' (crip (weld (l u) ":")) w]]
      --
  |=  u=@uxor
  ^-  wain
  =|  fot=(list wain)
  =/  fox=(list @uxor)  [u ~]
  =/  fen  (~(gas in *(set @uxor)) fox)
  |-  ^-  wain
  ?~  fox
    (zing (join `wain`['\0a' ~] fot))
  =/  p=pile  (~(got by hill.fuji) i.fox)
  =|  xof=(list @uxor)
  =|  bot=(list wain)
  =|  xob=(list @uwoo)
  =/  box=(list @uwoo)  [0w1 ~]
  =/  ben  (~(gas in *(set @uwoo)) box)
  |-  ^-  wain
  ?~  box
    ?.  =(~ xob)
      $(box (flop xob), xob ~)
    =/  fun=wain  (zing (flop [`wain`['}' ~] bot]))
    ::  NB: this rendering of block 0w0 depends on +fuse:py
    =.  fun  (welp ['/*' +>+:(c-blob 0w0 (~(got by will.p) 0w0))] ['*/' fun])
    =.  fun
      :*  (crip ['/' '/' ' ' ' ' (n q:(~(got by peal.fuji) bell.p))])
          '//'
          (crip "NOUN_DECL {(f i.fox)}({(d-args walt.p)}) \{")
          fun
      ==
    =/  n  norm:(puck bell.p)
    =?  fun  ?=(^ seat.n)
      :*  '//    as called from:'
          (crip ['/' '/' ' ' ' ' ' ' ' ' ~(ram re (ren:blot:sack u.seat.n))])
          '//'
          fun
      ==
    =?  fun  ?=(^ area.n)
      [(crip ['/' '/' ' ' ' ' ~(ram re (ren:blot:sack u.area.n))]) fun]
    ^$(fot [fun fot], fox (weld (flop xof) t.fox))
  =/  [ux=(unit @uxor) uw=(pair (unit @uwoo) (unit @uwoo)) wa=wain]
    (c-blob i.box (~(got by will.p) i.box))
  =.  ux  `(unit @uxor)`?:(|(?=(~ ux) (~(has in fen) u.ux)) ~ `u.ux)
  =.  p.uw  `(unit @uwoo)`?:(|(?=(~ p.uw) (~(has in ben) u.p.uw)) ~ `u.p.uw)
  =.  q.uw  `(unit @uwoo)`?:(|(?=(~ q.uw) (~(has in ben) u.q.uw)) ~ `u.q.uw)
  %=  $
    xof  ?~(ux xof [u.ux xof])
    fen  ?~(ux fen (~(put in fen) u.ux))
    bot  [wa bot]
    box  ?~(p.uw t.box [u.p.uw t.box])
    xob  ?~(q.uw xob [u.q.uw xob])
    ben  (~(gas in ben) (weld (drop p.uw) (drop q.uw)))
  ==
--
