/-  gene
|.
=>  $:gene
=*  sack  +3
=*  moan  moan.sack
=*  cole  cole.sack
=|  =fuji
=>
|%
::    get analysis result by bell
::
++  puck
  |=  b=bell
  =>  [b=b m=moan ..hone]
  ~+
  =/  h  (~(get ja m) form.b)
  |-  ^-  (unit hone)  :: XX just hone?
  ?<  ?=(~ h)
  ?:  =(text.b soot.i.h)  `i.h
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
    ?<  ?=(~ hues)
    =/  team  (~(gas in *(set bell)) ~(val by ices.norm.u.hues))
    =.  team  (~(dif in team) loop.norm.u.hues)
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
::  sans: next SSA register
::  redo: arms called without knowing registerization
::  fuji: code table
::
+$  gen  [sans=@uvre redo=(list [t=bell b=@uwoo]) =^fuji]
::
++  jean
  |_  [=gen like=(map bell need)]
  ::
  ::    core DDCG linearizer
  ::
  ++  cuts
    =/  =goal  [%done ~]
    |=  =bell
    =/  h  (puck bell)
    ?<  ?=(~ h)
    =*  n  nomm.norm.u.h
    |-  ^-  [next _gen]
    ?-  -.n
        %par
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  loch  gen  (emit ~ ~ %don last)
        $(goal [%next [%this last] loch])
      ::
          %pick
        (mine sass.goal zero.goal)
      ::
          %next
        =^  [bill=@uwoo left=need rite=need]  gen  (lyse goal)
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
        (mine sass.goal zero.goal)
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
      =/  bull  (~(get by ices.norm.u.h) rail.n)
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
      ::  XX we need a placeholder for the @uwoo for a recursive call
      =/  hope  (~(get by call.cole) u.bull)
      =^  a  gen  (args u.bull)
      =/  wool=@uwoo
        ?.  r.a  (~(got by peal.fuji.gen) u.bull)
        `@`0
      ?-  -.goal
          %done
        =^  [dire=@uwoo seed=need]  gen
          ?~  hope
            =^  dike  gen  (emit ~ ~ %jmp wool v.a)
            =?  redo.gen  r.a  [[u.bull dike] redo.gen]
            [[dike n.a] gen]
          =^  s  gen  rain
          =^  dial  gen  (emit ~ ~ %jmf wool v.a s u.hope)
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
            =^  dine  gen  (emit ~ ~ %cal wool v.a salt post)
            =?  redo.gen  r.a  [[u.bull dine] redo.gen]
            [[dine n.a] gen]
          =^  s  gen  rain
          =^  dime  gen  (emit ~ ~ %caf wool v.a salt post s u.hope)
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
        =^  barf  gen  rain
        =^  tear  gen  (emit ~ [%imm 0 last]~ %don last)
        =^  fear  gen  (emit ~ [%imm 1 hasp]~ %don hasp)
        $(goal [%pick barf tear fear])
      ::
          %next
        ?:  ?=(%both -.what.goal)  (mine sass.what.goal then.goal)
        ::  no need for check if result unused
        ?:  ?=(%none -.what.goal)
          $(n pell.n)
        =^  tare  gen  rain
        =^  tile  gen  vial
        =^  fare  gen  rain
        =^  file  gen  vial
        =^  thin  gen
          %:  emit
            %:  ~(put by *(map @uvre (map @uwoo @uvre)))
                sass.what.goal
                (~(gas by *(map @uwoo @uvre)) ~[[tile tare] [file fare]])
            ==
            ~
            %hop  then.goal
          ==
        =^  tear  gen  (come tile thin)
        =^  fear  gen  (come file thin)
        =^  celt  gen  (emit ~ [%imm 0 tare]~ %hop tear)
        =^  felt  gen  (emit ~ [%imm 1 fare]~ %hop fear)
        =^  barf  gen  rain
        $(goal [%pick barf celt felt])
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
        ?:  ?=(%both -.what.goal)  (mine sass.what.goal then.goal)
        =^  rink  gen
          ?:  ?=(%none -.what.goal)
            rain
          [sass.what.goal gen]
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
        =^  crap  gen  rain
        $(goal [%pick crap reek riff])
      ::
          %next
        ?:  ?=(%both -.what.goal)  (mine sass.what.goal then.goal)
        ?:  ?=(%none -.what.goal)
          =^  than  gen  $(n that.n)
          =^  thin  gen  $(n this.n, then.goal then.than)
          (copy thin what.than)
        =^  tare  gen  rain
        =^  till  gen  vial
        =^  fare  gen  rain
        =^  fill  gen  vial
        =^  ward  gen
          %:  emit
            %:  ~(put by *(map @uvre (map @uwoo @uvre)))
                sass.what.goal
                (~(gas by *(map @uwoo @uvre)) ~[[till tare] [fill fare]])
            ==
            ~
            %hop
            then.goal
          ==
        =^  weir  gen  (come till ward)
        =^  mere  gen  (come fill ward)
        =^  ware  gen  (emit ~ [%imm 0 tare]~ %hop weir)
        =^  mare  gen  (emit ~ [%imm 1 fare]~ %hop mere)
        =^  crap  gen  rain
        $(goal [%pick crap ware mare])
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
        =^  lead  gen  rain
        =^  cond  gen  $(n what.n, goal [%pick lead tile file])
        (copy cond bead)
      =^  fest  gen  $(n else.n)
      =^  zest  gen  $(n then.n)
      =^  [bead=need tile=@uwoo file=@uwoo]  gen  (sect zest fest)
      =^  barf  gen  rain
      =^  tool  gen  (emit ~ [%ipb ~[barf]]~ %hop tile)
      =^  cond  gen
        $(n what.n, goal [%pick barf tool file])
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
        ?.  =(here.n 1)  (mine sass.goal zero.goal)
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
          =^  race  gen  $(n then.n, goal [%pick sass.goal tome foam])
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
        =^  mane  gen  rain
        ?-  -.goal
            %done
          =^  real  gen  $(n then.n)
          =^  dint  gen  (emit ~ [%men hint.n mane]~ %hop then.real)
          =^  fake  gen  $(n vice.n, goal [%next [%this mane] dint])
          (copy fake what.real)
        ::
            %pick
          =^  tame  gen  (emit ~ [%man ~]~ %hop zero.goal)
          =^  fame  gen  (emit ~ [%man ~]~ %hop once.goal)
          =^  real  gen  $(n then.n, goal [%pick sass.goal tame fame])
          =^  dint  gen  (emit ~ [%men hint.n mane]~ %hop then.real)
          =^  fake  gen  $(n vice.n, goal [%next [%this mane] dint])
          (copy fake what.real)
        ::
            %next
          =^  rugs  gen  (emit ~ [%man ~]~ %hop then.goal)
          =^  real  gen  $(n then.n, then.goal rugs)
          =^  dint  gen  (emit ~ [%men hint.n mane]~ %hop then.real)
          =^  fake  gen  $(n vice.n, goal [%next [%this mane] dint])
          (copy fake what.real)
        ==
      ::
          ?(%live %slog)
        =^  clue  gen  rain
        =^  real  gen  $(n then.n)
        =^  wave  gen
          ?:  ?=(%live hint.n)
            (emit ~ [%hit clue]~ %hop then.real)
          (emit ~ [%slg clue]~ %hop then.real)
        =^  fake  gen  $(n vice.n, goal [%next [%this clue] wave])
        (copy fake what.real)
      ::
          %memo
        =/  fork  (~(got by fizz.norm.u.h) hare.n)
        =^  funk  gen  rain
        =^  sunk  gen  rain
        =^  gunk  gen  rain
        =/  body=(list pole)  ~[[%imm 0 gunk] [%imm fork funk]]
        ?-  -.goal
            %done
          =^  salt  gen  rain
          =^  mode  gen  (emit ~ ~ %don salt)
          $(goal [%next [%this salt] mode])
        ::
            %pick
          =^  mere  gen  rain
          =^  chit  gen  (emit ~ ~ %brn mere zero.goal once.goal)
          =^  loot  gen  rain
          =^  root  gen  rain
          =^  loam  gen  (emit ~ ~[[%imm 0 loot] [%mew gunk sunk funk loot]] %hop zero.goal)
          =^  rome  gen  (emit ~ ~[[%imm 1 root] [%mew gunk sunk funk root]] %hop once.goal)
          =^  moog  gen  $(n then.n, zero.goal loam, once.goal rome)
          =^  cast  gen  (emit ~ body %mer gunk sunk funk mere chit then.moog)
          =^  fake  gen  $(n vice.n, goal [%next [%none ~] cast])
          =^  fear  gen  (copy fake what.moog)
          (copy fear [%this sunk])
        ::
            %next
          =^  [chit=next miss=next]    gen  (phil goal)
          =^  [chin=@uwoo mere=@uvre]  gen  (kerf chit)
          =^  [misc=@uwoo salt=@uvre]  gen  (kerf miss)
          =^  meow  gen  (emit ~ [%mew gunk sunk funk salt]~ %hop misc)
          =^  real  gen  $(n then.n, goal [%next [%this salt] meow])
          =^  cake  gen  (emit ~ body %mer gunk sunk funk mere chin misc)
          =^  fake  gen  $(n vice.n, goal [%next [%none ~] cake])
          =^  cope  gen  (copy fake what.real)
          (copy cope [%this sunk])
        ==
      ::
          %bout  ~|  %todo  !!
      ==
    ::
        %elf
      ?-  -.goal
          %done
        =^  last  gen  rain
        =^  deft  gen  (emit ~ ~ %don last)
        $(goal [%next [%this last] deft])
      ::
          %pick
        =^  flip  gen  rain
        =^  heft  gen  (emit ~ ~ %brn flip [zero once]:goal)
        $(goal [%next [%this flip] heft])
      ::
          %next
        =^  [weft=@uwoo good=@uvre]  gen  (kerf goal)
        =^  home  gen  rain
        =^  path  gen  rain
        =^  show  gen  (emit ~ ~ %spy home path good weft)
        =^  trot  gen  $(n walk.n, goal [%next [%this path] show])
        =^  paid  gen  $(n rent.n, goal [%next [%this home] then.trot])
        (copy paid what.trot)
      ==
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
    =/  blob  (~(got by hill.fuji.gen) u)
    =/  wool  (~(got by peal.fuji.gen) bell)
    ?+  -.bend.blob  ~|  %redo-cant  !!
        %cal
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      ?>  (~(has by like) bell)  :: XX fix
      =^  urge  gen  (args bell)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      =.  hill.fuji.gen  (~(del by hill.fuji.gen) u)
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ::
        %caf
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      ?>  (~(has by like) bell)  :: XX fix
      =^  urge  gen  (args bell)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      =.  hill.fuji.gen  (~(del by hill.fuji.gen) u)
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ::
        %jmp
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      ?>  (~(has by like) bell)  :: XX fix
      =^  urge  gen  (args bell)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      =.  hill.fuji.gen  (~(del by hill.fuji.gen) u)
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ::
        %jmf
      ?>  ?=(^ v.bend.blob)
      ?>  ?=(~ t.v.bend.blob)
      ?>  (~(has by like) bell)  :: XX fix
      =^  urge  gen  (args bell)
      =^  reed  gen  (emit ~ ~ bend.blob(a wool, v v.urge))
      =^  [rush=@uwoo i=@uvre]  gen  (kerf [%next n.urge reed])
      =.  hill.fuji.gen  (~(del by hill.fuji.gen) u)
      (emir u ~ [%mov i.v.bend.blob i]~ %hop rush)
    ==
  ::  +kerf: split single register into goal
  ::
  ::    given a destination, generate code which splits a noun in one
  ::    register to the registers described by the $need, and return the
  ::    one register and a label for the splitting code
  ::
  ++  kerf
    |=  =next
    ^-  [[@uwoo @uvre] _gen]
    =^  ir  gen  (kern ~ what.next)
    ?~  pose.ir
      [[then.next out.ir] gen]
    =^  thin  gen  (emit ~ (flop pose.ir) %hop then.next)
    [[thin out.ir] gen]
  ::  +kern: split register to need (instruction list)
  ::
  ::    like +kerf but return (reversed) instruction list
  ::    instead of emitting basic block
  ::
  ++  kern
    |=  [pose=(list pole) =need]
    ^-  [[pose=(list pole) out=@uvre] _gen]
    =/  tack=(list _need)  ~[need]
    =/  ui  (sass need)
    ?~  ui
      =^  crap  gen  rain
      [[~ crap] gen]
    |-  ^-  [[pose=(list pole) out=@uvre] _gen]
    ?~  tack
      [[pose u.ui] gen]
    =*  n  i.tack
    ?:  ?=(%both -.n)
      =/  lure  (sass left.n)
      =/  rule  (sass rite.n)
      =?  pose  ?=(^ lure)
        [[%hed sass.n u.lure] pose]
      =?  pose  ?=(^ rule)
        [[%tal sass.n u.rule] pose]
      $(tack [left.n rite.n t.tack])
    $(tack t.tack)
  ::
  ++  emit                                              ::  add block
    |=  =blob
    ^-  [@uwoo _gen]
    =^(l gen vial [l (emir l blob)])
  ::
  ++  emir                                              ::  put block
    |=  [l=@uwoo =blob]
    ^+  gen
    gen(hill.fuji (~(put by hill.fuji.gen) l blob))
  ::
  ++  rain                                              ::  new register
    ^-  [@uvre _gen]
    [sans.gen gen(sans .+(sans.gen))]
  ::  +lyse: split need for cons
  ::
  ++  lyse
    |=  =next
    ^-  [[@uwoo need need] _gen]
    ?-  -.what.next
        %both :: discards sick flag which is OK since we know we will fulfill the need
      [[then.next left.what.next rite.what.next] gen]
    ::
        %none
      [[then.next [%none ~] %none ~] gen]
    ::
        %this
      =^  l  gen  rain
      =^  r  gen  rain
      =^  lizz  gen  (emit ~ [%con l r sass.what.next]~ %hop then.next)
      [[lizz [%this l] [%this r]] gen]
    ==
  ::  +sass:  outermost register
  ::
  ++  sass
    |=  =need
    ^-  (unit @uvre)
    ?-  -.need
      %this  `sass.need
      %both  `sass.need
      %none  ~
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
    =|  lose=(list pole)
    =|  rose=(list pole)
    =/  tack=(list (each r=@uvre [z=need o=need]))  [%| what.zero what.once]~
    =|  salt=(list need)
    |-  ^-  [[need @uwoo @uwoo] _gen]
    ?~  tack
      ?>  ?=(^ salt)
      ?>  ?=(~ t.salt)
      =^  loan  gen  (emit ~ (flop lose) %hop then.zero)
      =^  roan  gen  (emit ~ (flop rose) %hop then.once)
      [[i.salt loan roan] gen]
    ?-  -.i.tack
        %&
      ?>  ?=(^ salt)
      ?>  ?=(^ t.salt)
      $(tack t.tack, salt [[%both p.i.tack i.t.salt i.salt] t.t.salt])
    ::
        %|
      ?:  ?=(%none -.z.p.i.tack)
        :: z side has no requirements
        :: so we should do no splitting outside conditional
        ?:  ?=(%none -.o.p.i.tack)
          $(tack t.tack, salt [[%none ~] salt])
        =^  rr  gen  (kern rose o.p.i.tack)
        =.  rose  pose.rr
        $(tack t.tack, salt [[%this out.rr] salt])
      ?:  ?=(%none -.o.p.i.tack)
        :: o side has no requirements
        :: so we should do no splitting outside conditional
        =^  lr  gen  (kern lose z.p.i.tack)
        =.  lose  pose.lr
        $(tack t.tack, salt [[%this out.lr] salt])
      ?:  ?=(%both -.z.p.i.tack)
        ::  z side splits
        ?:  ?=(%both -.o.p.i.tack)
          ::  both sides split, recursively build need
          %=  $
              tack
            :*  [%| left.z.p.i.tack left.o.p.i.tack]
                [%| rite.z.p.i.tack rite.o.p.i.tack]
                [%& sass.z.p.i.tack]
                t.tack
            ==
          ::
            rose  [[%mov sass.z.p.i.tack sass.o.p.i.tack] rose]
          ==
        ::  z side splits, o side this
        =^  lr  gen  (kern ~ z.p.i.tack)
        =.  lose  [[%mov sass.o.p.i.tack out.lr] lose]
        =.  lose  (weld pose.lr lose)
        $(tack t.tack, salt [o.p.i.tack salt])
      ?:  ?=(%both -.o.p.i.tack)
        ::  z side this, o side splits
        =^  rr  gen  (kern ~ o.p.i.tack)
        =.  rose  [[%mov sass.z.p.i.tack out.rr] rose]
        =.  rose  (weld pose.rr rose)
        $(tack t.tack, salt [z.p.i.tack salt])
      ::  both sides this
      =.  rose  [[%mov sass.z.p.i.tack sass.o.p.i.tack] rose]
      $(tack t.tack, salt [z.p.i.tack salt])
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
    =|  pose=(list pole)
    =/  tack=(list (each @uvre [l=need r=need]))  [%| what.feed seed]~
    =|  rack=(list need)
    |-  ^-  [next _gen]
    ?~  tack
      ?>  ?=(^ rack)
      ?>  ?=(~ t.rack)
      =^  cody  gen  (emit ~ pose %hop then.feed)
      [[%next i.rack cody] gen]
    ?:  ?=(%& -.i.tack)
      ?>  ?=(^ rack)
      ?>  ?=(^ t.rack)
      $(rack [[%both p.i.tack i.t.rack i.rack] t.t.rack], tack t.tack)
    ?:  ?=(%none -.l.p.i.tack)  $(rack [r.p.i.tack rack], tack t.tack)
    ?:  ?=(%none -.r.p.i.tack)  $(rack [l.p.i.tack rack], tack t.tack)
    ?:  ?=(%this -.l.p.i.tack)
      ?:  ?=(%this -.r.p.i.tack)
        :: both this
        =?  pose  ?!  .=  sass.l.p.i.tack  sass.r.p.i.tack
          [[%mov sass.l.p.i.tack sass.r.p.i.tack] pose]
        $(rack [l.p.i.tack rack], tack t.tack)
      :: left this, right both
      ::
      :: this case must be handled this way in case the code that needs
      :: l.p.i.tack will crash explicitly in some way.
      =^  rr  gen  (kern ~ r.p.i.tack)
      =.  pose  (weld (flop pose.rr) pose)
      =?  pose  ?!(=(sass.l.p.i.tack out.rr))
        [[%mov sass.l.p.i.tack out.rr] pose]
      $(tack t.tack, rack [[%this sass.l.p.i.tack] rack])
    ?:  ?=(%both -.r.p.i.tack)
      :: both both
      %=  $
          pose  [[%mov sass.l.p.i.tack sass.r.p.i.tack] pose]
          tack
        :*  [%| left.l.p.i.tack left.r.p.i.tack]
            [%| rite.l.p.i.tack rite.r.p.i.tack]
            [%& sass.l.p.i.tack]
            t.tack
        ==
      ==
    ::  left both, right this
    =/  lu  (sass left.l.p.i.tack)
    =/  ru  (sass rite.l.p.i.tack)
    =^  l  gen  ?~(lu rain [u.lu gen])
    =^  r  gen  ?~(ru rain [u.ru gen])
    %=  $
      pose  [[%con l r sass.r.p.i.tack] pose]
      tack
      :*  [%| left.l.p.i.tack %this l]
          [%| rite.l.p.i.tack %this r]
          [%& sass.l.p.i.tack]
          t.tack
      ==
    ==
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
    =^  mile  gen  (emit ~ [%poi r]~ %hop t)
    [[%next [%none ~] t] gen]
  ::
  ++  vial                                              ::  new label
    ^-  [@uwoo _gen]
    ?^  free.fuji.gen
      [i.free.fuji.gen gen(free.fuji t.free.fuji.gen)]
    [next.fuji.gen gen(next.fuji +(next.fuji.gen))]
  ::
  ++  come                                              ::  label come-from
    |=  [f=@uwoo t=@uwoo]
    ^-  [@uwoo _gen]
    [f (emir f [~ ~ %hip f t])]
  ::  +phil: generate phi nodes
  ::
  ::    given a destination common to two branches, generate a phi node
  ::    and come-from blocks
  ::
  ++  phil
    |=  =next
    ^-  [[^next ^next] _gen]
    =/  tack=(list (each [zp=@uvre op=@uvre] need))  [%| what.next]~
    =|  salt=(list [z=need o=need])
    =|  biff=(map @uvre (map @uwoo @uvre))
    =^  zb  gen  vial
    =^  ob  gen  vial
    |-  ^-  [[_next _next] _gen]
    ?~  tack
      ?>  ?=(^ salt)
      ?>  ?=(~ t.salt)
      =^  fill  gen  (emit biff ~ %hop then.next)
      =^  zeke  gen  (come zb fill)
      =^  oaks  gen  (come ob fill)
      [[[%next z.i.salt zeke] [%next o.i.salt oaks]] gen]
    ?-  -.i.tack
        %&
      ?>  ?=(^ salt)
      ?>  ?=(^ t.salt)
      %=  $
          tack  t.tack
          salt
        :_  t.t.salt
        :-  [%both zp.p.i.tack z.i.t.salt z.i.salt]
        [%both op.p.i.tack o.i.t.salt o.i.salt]
      ==
    ::
        %|
      ?-  -.p.i.tack
          %none  $(salt [[[%none ~] %none ~] salt], tack t.tack)
          %this
        =^  l  gen  rain
        =^  r  gen  rain
        =/  phi  (~(gas by *(map @uwoo @uvre)) ~[[zb l] [ob r]])
        %=  $
            biff  (~(put by biff) sass.p.i.tack phi)
            tack  t.tack
            salt  [[[%this l] %this r] salt]
        ==
      ::
          %both
        =^  hurl  gen  rain
        =^  barf  gen  rain
        =/  phi  (~(gas by *(map @uwoo @uvre)) ~[[zb hurl] [ob barf]])
        %=  $
            biff  (~(put by biff) sass.p.i.tack phi)
            tack
          :*  [%| left.p.i.tack]
              [%| rite.p.i.tack]
              [%& hurl barf]
              t.tack
          ==
        ==
      ==
    ==
  ::  +args: look up subject registerization
  ::
  ::    when we emit code for a direct call, we hope to know the
  ::    registerization already. If we don't, we need to add the call to
  ::    the redo set. If we do, then we need a linear list of poison
  ::    registers and a linear list of argument registers, as well as a
  ::    need which describes which parts of the call subject go in which
  ::    registers
  ::
  ++  args
    |=  =bell
    ^-  [[v=(list @uvre) n=need r=?] _gen]
    =/  cn  (~(get by like) bell)
    =?  cn  ?=(~ cn)
      =/  dn  (~(get by gist.fuji.gen) bell)
      ?~  dn  ~
      `want.u.dn
    ?~  cn
      =^  s  gen  rain
      [[~[s] [%this s] &] gen]
    =^  s  gen  (scar u.cn)
    [[v n |]:s gen]
  ::  +scar: generate fresh parameter lists
  ::
  ::    generate fresh parameter variables and provide them both in
  ::    argument list and need form
  ::
  ++  scar
    |=  n=need
    =|  rv=(list @uvre)
    =/  tack=(list (each @uvre need))  [%| n]~
    =|  salt=(list need)
    |-  ^-  [[v=(list @uvre) n=need] _gen]
    ?~  tack
      ?>  ?=(^ salt)
      ?>  ?=(~ t.salt)
      [[(flop rv) i.salt] gen]
    ?-  -.i.tack
        %&
      ?>  ?=(^ salt)
      ?>  ?=(^ t.salt)
      $(tack t.tack, salt [[%both p.i.tack i.t.salt i.salt] t.t.salt])
    ::
        %|
      ?-  -.p.i.tack
          %both
        =^  br  gen  rain
        %=  $
            tack
          :*  [%| left.p.i.tack]
              [%| rite.p.i.tack]
              [%& br]
              t.tack
          ==
        ==
      ::
          %none  $(tack t.tack, salt [[%none ~] salt])
          %this
        =^  vr  gen  rain
        $(rv [vr rv], salt [[%this vr] salt], tack t.tack)
      ==
    ==
  ::  +from: push need down by axis
  ::
  ++  from
    |=  [axe=@ =next]
    ^-  [^next _gen]
    ?<  =(0 axe)
    =^  crap  gen
      =/  crop  (sass what.next)
      ?~  crop  rain
      [u.crop gen]
    =?  what.next  ?=(%none -.what.next)  [%this crap]
    =|  bait=(list [r=@uvre c=?(%2 %3)])
    |-  ^-  [_next _gen]
    ?.  =(1 axe)
      =^  barf  gen  rain
      $(bait [[barf (cap axe)] bait], axe (mas axe))
    =/  bits  (turn bait |=([r=@uvre *] r))
    =^  fram  gen  (emit ~ [%ipb ~[crap]]~ %hop then.next)
    =/  feed
      %+  roll  bait
      |=  [[r=@uvre c=?(%2 %3)] n=_what.next]
      ?-  c
        %2  [%both r n %none ~]
        %3  [%both r [%none ~] n]
      ==
    [[%next feed fram] gen]
  ::  +into: split need for edit
  ::
  ::    first returned need is for the patch noun,
  ::    the second is for the noun to be edited
  ::
  ++  into
    |=  [axe=@ =next]
    ^-  [[need need @uwoo] _gen]
    =*  twig  what.next
    =|  tres=(list [lr=?(%2 %3) p=@uvre =need])
    =|  pose=(list pole)
    ?<  =(0 axe)
    |-  ^-  [[need need @uwoo] _gen]
    ?.  =(1 axe)
      =^  p  gen  rain
      ?-  (cap axe)
          %2
        ?-  -.twig
            %both
          %=  $
            tres  [[%2 p rite.twig] tres]
            twig  left.twig
            axe   (mas axe)
            pose  [[%mov p sass.twig] pose]
          ==
        ::
            %this
          =^  l  gen  rain
          =^  r  gen  rain
          %=  $
            tres  [[%2 p %this r] tres]
            twig  [%this l]
            axe   (mas axe)
            pose  [[%con l r sass.twig] pose]
          ==
        ::
            %none
          %=  $
            tres  [[%2 p %none ~] tres]
            axe   (mas axe)
          ==
        ==
      ::
          %3
        ?-  -.twig
            %both
          %=  $
            tres  [[%3 p left.twig] tres]
            twig  rite.twig
            axe   (mas axe)
            pose  [[%mov p sass.twig] pose]
          ==
        ::
            %this
          =^  l  gen  rain
          =^  r  gen  rain
          %=  $
            tres  [[%3 p %this l] tres]
            twig  [%this r]
            axe   (mas axe)
            pose  [[%con l r sass.twig] pose]
          ==
        ::
            %none
          %=  $
            tres  [[%3 p %none ~] tres]
            axe   (mas axe)
          ==
        ==
      ==
    =^  flag  gen  rain
    =/  tree=need  [%this flag]
    |-  ^-  [[need need @uwoo] _gen]
    ?~  tres
      =^  tint  gen  (emit ~ [[%ipb ~[flag]] pose] %hop then.next)
      [[twig tree tint] gen]
    ?-  lr.i.tres
        %2
      $(tres t.tres, tree [%both p.i.tres tree need.i.tres])
    ::
        %3
      $(tres t.tres, tree [%both p.i.tres need.i.tres tree])
    ==
  ::  +mede: split immediate into registers of need
  ::
  ++  mede
    |=  [u=@uwoo n=* =need]
    ^-  [@uwoo _gen]
    =|  todo=(list pole)
    =/  tack=(list [n=(unit *) =_need])  [`n need]~
    |-  ^-  [@uwoo _gen]
    ?~  tack
      (emit ~ todo %hop u)
    ?-  -.need.i.tack
        %none  $(tack t.tack)
        %this
      ?~  n.i.tack
        $(todo [[%poi sass.need.i.tack] todo], tack t.tack)
      $(todo [[%imm u.n.i.tack sass.need.i.tack] todo], tack t.tack)
      ::
        %both
      ?~  n.i.tack
        $(tack [[~ rite.need.i.tack] [~ left.need.i.tack] t.tack])
      ?@  u.n.i.tack
        $(tack [[~ rite.need.i.tack] [~ left.need.i.tack] t.tack])
      $(tack [[`+.u.n.i.tack rite.need.i.tack] [`-.u.n.i.tack left.need.i.tack] t.tack])
    ==
  --
::  +sill: list of registers from a need
::
++  sill
  |=  want=need
  =|  wart=(list @uvre)
  =/  tack=(list need)  ~[want]
  |-  ^-  (list @uvre)
  ?~  tack  wart
  ?-  -.i.tack
    %this  $(wart [sass.i.tack wart], tack t.tack)
    %both  $(tack [rite.i.tack left.i.tack t.tack])
    %none  $(tack t.tack)
  ==
::  +mill: loop over redos
::
::    run redo:jean on each arm in the redo list, which will generate
::    code to properly registerize callsites whose registerization was
::    deferred, without changing the registerization of the calling arm
::
++  mill
  =|  todo=(list [=bell dire=next =gen])
  =|  like=(map bell need)
  =/  toil  work
  =/  wurk  toil
  |-  ^+  fuji
  ?^  toil
    =/  [dire=next =gen]  (~(cuts jean [*@uvre ~ fuji] like) i.toil)
    %=  $
       toil  t.toil
       todo  [[i.toil dire gen] todo]
       like  (~(put by like) i.toil what.dire)
       fuji  %=  fuji.gen
               peal  (~(put by peal.fuji.gen) i.toil then.dire)
    ==       ==
  |-  ^+  fuji
  ?^  todo
    =/  r  redo.gen.i.todo
    |-  ^+  fuji
    ?^  r
      =.  gen.i.todo
        ~|  =*  bel  bell.i.todo
            =/  mot  (~(get ja moan) form.bel)
            |-  ^-  ?(%redo-fail ~)
            ?~  mot  ~
            ?:  =(soot.i.mot text.bel)
              ((outa:blot:sack "redo fail: " `@`0 [seat area]:norm.i.mot) %redo-fail)
            $(mot t.mot)
          (~(redo jean gen.i.todo(redo ~, fuji fuji) like) i.r)
      $(r t.r)
    =^  [wish=@uwoo sire=@uvre]  gen.i.todo  (~(kerf jean gen.i.todo(redo ~, fuji fuji) like) dire.i.todo)
    =*  f  fuji.gen.i.todo
    ?.  (~(has by hill.f) wish)  ~&  %missing-wish  !!
    =/  walt   (sill what.dire.i.todo)
    =/  =pile  [what.dire.i.todo walt sire sans.gen.i.todo]
    %=  ^$
      todo  t.todo
      fuji  %=  f
              gist  (~(put by gist.f) bell.i.todo pile)
              gong  (~(put by gong.f) bell.i.todo wish)
    ==      ==
  ::  XX temporary: turn hip/phi into mov so we can run this as-is
  ::  note that it's not safe to do mov coalescing on the output of this
  ::  since we may now have multiple %mov's that target one register
  =/  toil  wurk
  |-  ^+  fuji
  ?~  toil
    fuji
  %=  $
      toil  t.toil
  ::
      hill.fuji
    =/  =pile  (~(got by gist.fuji) i.toil)
    =/  seen
      %-  ~(gas in *(set @uwoo))
      :~  (~(got by peal.fuji) i.toil)
          (~(got by gong.fuji) i.toil)
      ==
    =/  queu=(list @uwoo)  ~(tap in seen)
    =|  back=(list @uwoo)
    !.
    |-  ^+  hill.fuji
    ?~  queu
      ?~  back  hill.fuji
      $(queu (flop back), back ~)

    =/  blob  (~(got by hill.fuji) i.queu)
    =^  more=(list @uwoo)  blob
      ?-  -.bend.blob
          %hip
        :-  ~[t.bend.blob]
        =/  movs
          %-  ~(rep by biff:(~(got by hill.fuji) t.bend.blob))
          |=  [[out=@uvre bin=(map @uwoo @uvre)] lit=(list pole)]
          [[%mov (~(got by bin) c.bend.blob) out] lit]
        [biff.blob (welp body.blob movs) %hop t.bend.blob]  :: XX flop?
      ::
          %clq  [~[z o]:bend.blob blob]
          %eqq  [~[z o]:bend.blob blob]
          %brn  [~[z o]:bend.blob blob]
          %hop  [~[t.bend.blob] blob]
          %lnk  [~[t.bend.blob] blob]
          %cal  [~[t.bend.blob] blob]
          %caf  [~[t.bend.blob] blob]
          %lnt  `blob
          %jmp  `blob
          %jmf  `blob
          %spy  [~[t.bend.blob] blob]
          %mer  [~[i m]:bend.blob blob]
          %don  `blob
          %bom  `blob
      ==
    |-  ^+  hill.fuji
    ?~  more
      ^$(queu t.queu, hill.fuji (~(put by hill.fuji) i.queu blob))
    ?:  (~(has in seen) i.more)
      $(more t.more)
    $(more t.more, back [i.more back], seen (~(put in seen) i.more))
  ==
--
=+  ver=%1
|%
++  this  .
::
++  peek
   |=  [s=* f=*]
    =/  moat  (~(get ja moan) f)
    |-  ^-  (unit [@uvre @uwoo ^fuji])  :: XX fix product type
    ?~  moat  ~
    ?.  (~(huge so:sack soot.i.moat) [& s])
      $(moat t.moat)
    ?~  u=(~(get by gong.fuji) [soot.i.moat f])
      ~|  %not-in-gong  !!
    =/  p
      ~|  %not-in-gist
      (~(got by gist.fuji) [soot.i.moat f])
    `[sire.p u.u fuji]
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
    =/  hole  ~(key by gist.fuji)
    ::  codegen
    =.  fuji  mill
    =/  heck  ~(key by gist.fuji)
    [(~(dif in heck) hole) (~(dif in hole) heck) this]
  ==
::
++  xray  ~|  %todo  !!
--
