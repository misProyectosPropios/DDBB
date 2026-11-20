var ee=Object.defineProperty;var te=(s,e,t)=>e in s?ee(s,e,{enumerable:!0,configurable:!0,writable:!0,value:t}):s[e]=t;var T=(s,e,t)=>te(s,typeof e!="symbol"?e+"":e,t);(function(){const e=document.createElement("link").relList;if(e&&e.supports&&e.supports("modulepreload"))return;for(const a of document.querySelectorAll('link[rel="modulepreload"]'))o(a);new MutationObserver(a=>{for(const d of a)if(d.type==="childList")for(const r of d.addedNodes)r.tagName==="LINK"&&r.rel==="modulepreload"&&o(r)}).observe(document,{childList:!0,subtree:!0});function t(a){const d={};return a.integrity&&(d.integrity=a.integrity),a.referrerPolicy&&(d.referrerPolicy=a.referrerPolicy),a.crossOrigin==="use-credentials"?d.credentials="include":a.crossOrigin==="anonymous"?d.credentials="omit":d.credentials="same-origin",d}function o(a){if(a.ep)return;a.ep=!0;const d=t(a);fetch(a.href,d)}})();function se(s){const e=document.createElement("article");e.className="blog-article",e.innerHTML=`
    <header class="article-header">
      <div class="breadcrumb">DDBB Notes / Overview</div>
      <h1>Database Internals, Step by Step</h1>
      <p class="article-lead">
        An interactive handbook for relational and NoSQL database internals — recovery logging,
        schedulers, concurrency control, isolation levels, and schema design — backed by formal
        correctness proofs in Dafny.
      </p>
    </header>

    <section class="prose-section">
      <h2>Available Interactive Pages</h2>
      <p>
        We are building one topic at a time, starting with transaction recovery and logging.
        Use the sidebar on the left to browse the curriculum.
      </p>

      <div class="topic-card-grid">
        <div class="topic-card topic-card-ready">
          <div class="topic-card-eyebrow">Logging · Available Now</div>
          <h3>Undo Logging (Simple / Pure)</h3>
          <p>
            Define initial database variables (such as <code>X = 5</code>, <code>Y = 10</code>),
            build a schedule of transactions, inspect the generated Undo log records, trace
            <code>FLUSH LOG</code> and <code>OUTPUT</code> ordering (Rules U1 &amp; U2), and simulate crash recovery.
          </p>
          <button type="button" class="btn btn-primary" data-open-undo>
            Open Undo Logging →
          </button>
        </div>

        <div class="topic-card topic-card-muted">
          <div class="topic-card-eyebrow">Up Next</div>
          <h3>Redo, Undo/Redo &amp; Non-Quiescent Checkpointing</h3>
          <p>
            Additional logging strategies will plug into the same double-dispatch
            <code>LoggingStrategy</code> architecture without changing schedule definitions.
          </p>
        </div>
      </div>
    </section>
  `;const t=e.querySelector("[data-open-undo]");return t==null||t.addEventListener("click",()=>s("undo")),e}const ae=[{title:"Logging",items:[{label:"Undo Logging",route:"undo",status:"active"},{label:"Redo Logging",status:"soon"},{label:"Undo / Redo Logging",status:"soon"},{label:"Checkpointing (Non-Quiescent)",status:"soon"}]},{title:"Scheduler & Concurrency",items:[{label:"Scheduler & Serializability",status:"soon"},{label:"Dependency Graphs",status:"soon"},{label:"Isolation Levels (RR, RC, CS)",status:"soon"},{label:"Deadlock Visualizer",status:"soon"},{label:"Optimistic & Pessimistic Control",status:"soon"},{label:"MVCC Simulator",status:"soon"}]},{title:"SQL Design & Internals",items:[{label:"DER to Generic SQL",status:"soon"},{label:"Triggers & Stored Procedures",status:"soon"},{label:"Normalization",status:"soon"}]},{title:"NoSQL",items:[{label:"DID",status:"soon"},{label:"DER to Column-Family",status:"soon"},{label:"DER to Workflow & Entities",status:"soon"}]}];function ne(s,e){const t=document.createElement("aside");t.className="sidebar",t.setAttribute("aria-label","DDBB Topics Navigation");const o=document.createElement("div");o.className="sidebar-brand";const a=document.createElement("button");a.type="button",a.className="brand-button",a.innerHTML=`
    <span class="brand-mark">DB</span>
    <span class="brand-copy">
      <span class="brand-title">DDBB Notes</span>
      <span class="brand-subtitle">Interactive Database Guide</span>
    </span>
  `,a.addEventListener("click",()=>e("overview")),o.appendChild(a),t.appendChild(o);const d=document.createElement("nav");d.className="sidebar-nav";const r=document.createElement("button");r.type="button",r.className=`nav-link nav-link-top${s==="overview"?" is-current":""}`,r.textContent="Overview",r.addEventListener("click",()=>e("overview")),d.appendChild(r);for(const m of ae){const S=document.createElement("div");S.className="nav-section";const w=document.createElement("div");w.className="nav-section-title",w.textContent=m.title,S.appendChild(w);const O=document.createElement("ul");O.className="nav-list";for(const C of m.items){const N=document.createElement("li");if(C.route){const f=document.createElement("button");f.type="button",f.className=`nav-link${s===C.route?" is-current":""}`,f.innerHTML=`
          <span class="nav-dot"></span>
          <span>${C.label}</span>
        `,f.addEventListener("click",()=>e(C.route)),N.appendChild(f)}else{const f=document.createElement("span");f.className="nav-item-disabled",f.setAttribute("aria-disabled","true"),f.innerHTML=`
          <span>${C.label}</span>
          <span class="nav-soon">Soon</span>
        `,N.appendChild(f)}O.appendChild(N)}S.appendChild(O),d.appendChild(S)}t.appendChild(d);const c=document.createElement("div");return c.className="sidebar-footer",c.innerHTML=`
    <span class="verified-pill">Verified in Dafny</span>
    <p>Algorithms mirror the formally verified specs in <code>dafny/logging/</code>.</p>
  `,t.appendChild(c),t}class X{constructor(e){T(this,"kind","START");this.tx=e}accept(e){e.visitStart(this.tx)}format(){return`START ${this.tx}`}}class H{constructor(e,t){T(this,"kind","READ");this.tx=e,this.element=t}accept(e){e.visitRead(this.tx,this.element)}format(){return`READ ${this.tx} ${this.element}`}}class G{constructor(e,t,o){T(this,"kind","WRITE");this.tx=e,this.element=t,this.newValue=o}accept(e){e.visitWrite(this.tx,this.element,this.newValue)}format(){return`WRITE ${this.tx} ${this.element} ${this.newValue}`}}class Y{constructor(e){T(this,"kind","COMMIT");this.tx=e}accept(e){e.visitCommit(this.tx)}format(){return`COMMIT ${this.tx}`}}class z{constructor(e){T(this,"kind","ABORT");this.tx=e}accept(e){e.visitAbort(this.tx)}format(){return`ABORT ${this.tx}`}}class oe{constructor(e){this.operations=e}generateLog(e){for(const t of this.operations)e.process(t);return e.getLog()}run(e){return{log:this.generateLog(e),trace:e.getTrace(),errors:e.getErrors()}}}function W(s){const e=[],t=[];return s.split(/[\n;]+/).map(a=>a.trim()).filter(a=>a.length>0&&!a.startsWith("//")&&!a.startsWith("#")).forEach((a,d)=>{const r=d+1,c=a.replace(/[(),]/g," ").split(/\s+/).filter(Boolean);if(c.length===0)return;switch(c[0].toUpperCase()){case"START":case"S":case"BEGIN":{if(c.length!==2){t.push(`Line ${r}: expected "START <Tx>" (got "${a}").`);return}e.push(new X(c[1]));break}case"READ":case"R":{if(c.length!==3){t.push(`Line ${r}: expected "READ <Tx> <Element>" (got "${a}").`);return}e.push(new H(c[1],c[2]));break}case"WRITE":case"W":{if(c.length!==4){t.push(`Line ${r}: expected "WRITE <Tx> <Element> <Integer>" (got "${a}").`);return}const S=Number(c[3]);if(!Number.isInteger(S)){t.push(`Line ${r}: WRITE value must be an integer (got "${c[3]}").`);return}e.push(new G(c[1],c[2],S));break}case"COMMIT":case"C":{if(c.length!==2){t.push(`Line ${r}: expected "COMMIT <Tx>" (got "${a}").`);return}e.push(new Y(c[1]));break}case"ABORT":case"A":case"ROLLBACK":{if(c.length!==2){t.push(`Line ${r}: expected "ABORT <Tx>" (got "${a}").`);return}e.push(new z(c[1]));break}default:t.push(`Line ${r}: unknown operation "${c[0]}". Use START, READ, WRITE, COMMIT, or ABORT.`)}}),{operations:e,parseErrors:t}}function I(s){return s.map(e=>e.format()).join(`
`)}function Q(s){switch(s.kind){case"LogStart":return`<START ${s.tx}>`;case"LogUndoUpdate":return`<${s.tx}, ${s.element}, ${s.oldValue}>`;case"LogCommit":return`<COMMIT ${s.tx}>`;case"LogAbort":return`<ABORT ${s.tx}>`}}function re(s){switch(s.kind){case"EventLog":return`LOG    ${Q(s.record)}`;case"EventRead":return`READ   ${s.tx}(${s.element}) => ${s.value}`;case"EventWriteBuffer":return`WRITE  ${s.tx}(${s.element}): ${s.oldVal} -> ${s.newVal} [buffer]`;case"EventUndoRestore":return`UNDO   ${s.tx}(${s.element}) := ${s.restoredVal} [buffer]`;case"EventFlushLog":return`FLUSH  LOG (up to record #${s.flushedCount})`;case"EventOutput":return`OUTPUT ${s.element} = ${s.value} [disk]`}}class ie{constructor(e){T(this,"_log",[]);T(this,"_trace",[]);T(this,"_errors",[]);T(this,"_disk");T(this,"_buffer");T(this,"_flushedLogLen",0);T(this,"_activeTxs",new Set);T(this,"_committedTxs",new Set);T(this,"_abortedTxs",new Set);T(this,"_dirtyElements",new Map);T(this,"_snapshots",[]);this._disk={...e},this._buffer={...e},this._snapshots.push(this.captureSnapshot(0,"Initial State",0))}get log(){return this._log}get trace(){return this._trace}get errors(){return this._errors}get flushedLogLen(){return this._flushedLogLen}get snapshots(){return this._snapshots}process(e){const t=this._trace.length;e.accept(this),this._snapshots.push(this.captureSnapshot(this._snapshots.length,e.format(),t))}visitStart(e){if(this._activeTxs.has(e)||this._committedTxs.has(e)||this._abortedTxs.has(e)){this._errors.push(`Cannot START ${e}: transaction was already started.`);return}const t={kind:"LogStart",tx:e};this._log.push(t),this._trace.push({kind:"EventLog",record:t}),this._activeTxs.add(e),this._dirtyElements.set(e,[])}visitRead(e,t){if(!this._activeTxs.has(e)){this._errors.push(`Cannot READ in ${e}: transaction is not active.`);return}if(!(t in this._buffer)){this._errors.push(`Cannot READ ${t} in ${e}: unknown database element.`);return}const o=this._buffer[t];this._trace.push({kind:"EventRead",tx:e,element:t,value:o})}visitWrite(e,t,o){if(!this._activeTxs.has(e)){this._errors.push(`Cannot WRITE in ${e}: transaction is not active.`);return}if(!(t in this._buffer)){this._errors.push(`Cannot WRITE ${t} in ${e}: unknown database element.`);return}const a=this._buffer[t],d={kind:"LogUndoUpdate",tx:e,element:t,oldValue:a};this._log.push(d),this._trace.push({kind:"EventLog",record:d}),this._buffer[t]=o,this._trace.push({kind:"EventWriteBuffer",tx:e,element:t,oldVal:a,newVal:o});const r=this._dirtyElements.get(e)??[];r.includes(t)||(r.push(t),this._dirtyElements.set(e,r))}flushLogIfNeeded(){this._flushedLogLen<this._log.length&&(this._flushedLogLen=this._log.length,this._trace.push({kind:"EventFlushLog",flushedCount:this._flushedLogLen}))}outputDirtyElements(e){const t=this._dirtyElements.get(e)??[];for(const o of t){const a=this._buffer[o];this._disk[o]=a,this._trace.push({kind:"EventOutput",element:o,value:a})}}emitCommitAndFinalize(e){const t={kind:"LogCommit",tx:e};this._log.push(t),this._trace.push({kind:"EventLog",record:t}),this._flushedLogLen=this._log.length,this._trace.push({kind:"EventFlushLog",flushedCount:this._flushedLogLen}),this._activeTxs.delete(e),this._committedTxs.add(e),this._dirtyElements.delete(e)}visitCommit(e){if(!this._activeTxs.has(e)){this._errors.push(`Cannot COMMIT ${e}: transaction is not active.`);return}this.flushLogIfNeeded(),this.outputDirtyElements(e),this.emitCommitAndFinalize(e)}rollbackTxBuffer(e){for(let t=this._log.length-1;t>=0;t--){const o=this._log[t];o.kind==="LogUndoUpdate"&&o.tx===e&&(this._buffer[o.element]=o.oldValue,this._trace.push({kind:"EventUndoRestore",tx:e,element:o.element,restoredVal:o.oldValue}))}}emitAbortAndFinalize(e){const t={kind:"LogAbort",tx:e};this._log.push(t),this._trace.push({kind:"EventLog",record:t}),this._flushedLogLen=this._log.length,this._trace.push({kind:"EventFlushLog",flushedCount:this._flushedLogLen}),this._activeTxs.delete(e),this._abortedTxs.add(e),this._dirtyElements.delete(e)}visitAbort(e){if(!this._activeTxs.has(e)){this._errors.push(`Cannot ABORT ${e}: transaction is not active.`);return}this.rollbackTxBuffer(e),this.emitAbortAndFinalize(e)}getLog(){return this._log}getTrace(){return this._trace}getErrors(){return this._errors}getFlushedLog(){return this._log.slice(0,this._flushedLogLen)}getDisk(){return{...this._disk}}getBuffer(){return{...this._buffer}}captureSnapshot(e,t,o){return{stepIndex:e,operationLabel:t,log:[...this._log],trace:[...this._trace],newTraceStart:o,errors:[...this._errors],flushedLogLen:this._flushedLogLen,disk:{...this._disk},buffer:{...this._buffer},activeTxs:Array.from(this._activeTxs),committedTxs:Array.from(this._committedTxs),abortedTxs:Array.from(this._abortedTxs)}}}function le(s){const e=new Set;for(const t of s)(t.kind==="LogCommit"||t.kind==="LogAbort")&&e.add(t.tx);return e}function ce(s,e){const t=le(e),o={...s},a=[],d=[],r=new Set;for(let c=e.length-1;c>=0;c--){const m=e[c];m.kind==="LogUndoUpdate"?!t.has(m.tx)&&m.element in o&&(o[m.element]=m.oldValue,d.push({kind:"RESTORE",tx:m.tx,element:m.element,oldValue:m.oldValue})):m.kind==="LogStart"&&!t.has(m.tx)&&!r.has(m.tx)&&(a.push({kind:"LogAbort",tx:m.tx}),r.add(m.tx),d.push({kind:"ABORT",tx:m.tx}))}return{recoveredDisk:o,recoveryAborts:a,actions:d}}const B=[{id:"xy-basic",label:"X=5, Y=10 (Commit & Abort)",description:"T1 updates X and commits; T2 updates Y and aborts.",variables:[{name:"X",value:5},{name:"Y",value:10}],scheduleText:["START T1","START T2","READ T1 X","WRITE T1 X 12","WRITE T2 Y 99","COMMIT T1","ABORT T2"].join(`
`)},{id:"garcia-molina",label:"Classic T1 (A=8, B=8 → 16)",description:"Garcia-Molina textbook example: T1 doubles A and B then commits.",variables:[{name:"A",value:8},{name:"B",value:8}],scheduleText:["START T1","READ T1 A","WRITE T1 A 16","READ T1 B","WRITE T1 B 16","COMMIT T1"].join(`
`)},{id:"crash-mid-tx",label:"Crash Mid-Transaction",description:"T1 commits X=50 while T2 writes Y=999 without committing yet.",variables:[{name:"X",value:5},{name:"Y",value:10}],scheduleText:["START T1","START T2","WRITE T1 X 50","WRITE T2 Y 999","COMMIT T1"].join(`
`)},{id:"invalid-ops",label:"Invalid Operations",description:"Demonstrates validation errors when writing before START or to unknown keys.",variables:[{name:"X",value:5}],scheduleText:["WRITE T1 X 20","START T1","WRITE T1 Z 99","WRITE T1 X 15","COMMIT T1"].join(`
`)}];function h(s){return s.replaceAll("&","&amp;").replaceAll("<","&lt;").replaceAll(">","&gt;").replaceAll('"',"&quot;").replaceAll("'","&#39;")}function de(s){switch(s.kind){case"LogStart":return"badge-start";case"LogUndoUpdate":return"badge-update";case"LogCommit":return"badge-commit";case"LogAbort":return"badge-abort"}}function ue(s){switch(s.kind){case"EventLog":return{label:"LOG",cls:"tag-log"};case"EventRead":return{label:"READ",cls:"tag-read"};case"EventWriteBuffer":return{label:"WRITE",cls:"tag-write"};case"EventUndoRestore":return{label:"UNDO",cls:"tag-undo"};case"EventFlushLog":return{label:"FLUSH",cls:"tag-flush"};case"EventOutput":return{label:"OUTPUT",cls:"tag-output"}}}function pe(){const s=document.createElement("article");s.className="blog-article";let e=B[0].variables.map($=>({...$})),t=W(B[0].scheduleText).operations,o=I(t),a=[],d="builder",r=null,c=null,m="WRITE",S="T1",w="X",O="12",C="",N="0",f="";function K(){const $={};for(const u of e)$[u.name]=u.value;return $}function Z(){const $=new ie(K());new oe(t).run($);const x=$.snapshots,b=x.length-1,R=r===null?b:Math.max(0,Math.min(r,b));return{snapshots:x,activeSnapshot:x[R]}}function E(){c=null}function g(){const{snapshots:$,activeSnapshot:u}=Z(),x=$.length-1,b=u.stepIndex,R=e.map(n=>n.name);R.length>0&&!w&&(m==="READ"||m==="WRITE")&&(w=R[0]),s.innerHTML=`
      <header class="article-header">
        <div class="breadcrumb">Logging / Undo Logging</div>
        <h1>Undo Logging</h1>
        <p class="article-lead">
          Pure (simple) Undo logging protects a database against crashes by recording the
          <strong>old value</strong> of every element before it is modified in memory, ensuring
          uncommitted writes can always be reversed.
        </p>

        <div class="callout-rules">
          <div class="rule-card">
            <span class="rule-pill">Rule U1 · WAL</span>
            <p>
              Before an updated element is written to disk (<code>OUTPUT</code>), its
              <code>&lt;T, X, oldVal&gt;</code> log record must already be flushed to disk
              (<code>FLUSH LOG</code>).
            </p>
          </div>
          <div class="rule-card">
            <span class="rule-pill">Rule U2 · Commit Order</span>
            <p>
              Before <code>&lt;COMMIT T&gt;</code> is written to the log and flushed, every
              element modified by <code>T</code> must already be written to disk
              (<code>OUTPUT</code>).
            </p>
          </div>
        </div>
      </header>

      <section class="workbench" aria-label="Interactive Undo Logging Workbench">
        <div class="presets-bar">
          <span class="presets-label">Examples:</span>
          <div class="presets-list">
            ${B.map(n=>`
              <button type="button" class="btn btn-chip" data-preset="${n.id}" title="${h(n.description)}">
                ${h(n.label)}
              </button>
            `).join("")}
          </div>
        </div>

        <div class="workbench-inputs">
          <!-- Initial Database State -->
          <div class="panel">
            <div class="panel-header">
              <h2>1. Initial Database State</h2>
              <span class="panel-meta">${e.length} element${e.length===1?"":"s"}</span>
            </div>
            <p class="panel-hint">Set the starting values stored on disk and in the memory buffer (e.g., <code>X = 5</code>, <code>Y = 10</code>).</p>

            <div class="var-list">
              ${e.length===0?'<div class="empty-inline">No database elements yet. Add one below.</div>':e.map((n,v)=>`
                <div class="var-chip">
                  <span class="var-name">${h(n.name)}</span>
                  <span class="var-eq">=</span>
                  <input
                    type="number"
                    step="1"
                    class="var-value-input"
                    value="${n.value}"
                    data-var-index="${v}"
                    aria-label="Value of ${h(n.name)}"
                  />
                  <button
                    type="button"
                    class="icon-btn"
                    data-remove-var="${v}"
                    title="Remove ${h(n.name)}"
                    aria-label="Remove ${h(n.name)}"
                  >×</button>
                </div>
              `).join("")}
            </div>

            <form class="inline-form" data-add-var-form>
              <input
                type="text"
                class="input input-sm"
                name="varName"
                placeholder="Element (e.g. Z)"
                value="${h(C)}"
                autocomplete="off"
              />
              <input
                type="number"
                step="1"
                class="input input-sm input-num"
                name="varValue"
                placeholder="Value"
                value="${h(N)}"
              />
              <button type="submit" class="btn btn-secondary">Add Variable</button>
            </form>
            ${f?`<div class="inline-error">${h(f)}</div>`:""}
          </div>

          <!-- Schedule Builder -->
          <div class="panel">
            <div class="panel-header">
              <h2>2. Schedule</h2>
              <div class="segmented" role="tablist" aria-label="Schedule input mode">
                <button
                  type="button"
                  class="segmented-btn${d==="builder"?" is-active":""}"
                  data-mode="builder"
                >Builder</button>
                <button
                  type="button"
                  class="segmented-btn${d==="text"?" is-active":""}"
                  data-mode="text"
                >Text</button>
              </div>
            </div>

            ${d==="builder"?`
              <form class="op-builder-form" data-add-op-form>
                <select class="input input-sm" name="opKind" aria-label="Operation type">
                  ${["START","READ","WRITE","COMMIT","ABORT"].map(n=>`<option value="${n}"${n===m?" selected":""}>${n}</option>`).join("")}
                </select>

                <input
                  type="text"
                  class="input input-sm input-tx"
                  name="opTx"
                  placeholder="Tx (e.g. T1)"
                  value="${h(S)}"
                  aria-label="Transaction ID"
                  autocomplete="off"
                />

                ${m==="READ"||m==="WRITE"?`
                  <input
                    type="text"
                    class="input input-sm input-elem"
                    name="opElement"
                    list="db-elements-datalist"
                    placeholder="Element (e.g. X)"
                    value="${h(w)}"
                    aria-label="Database element"
                    autocomplete="off"
                  />
                  <datalist id="db-elements-datalist">
                    ${R.map(n=>`<option value="${h(n)}"></option>`).join("")}
                  </datalist>
                `:""}

                ${m==="WRITE"?`
                  <input
                    type="number"
                    step="1"
                    class="input input-sm input-num"
                    name="opValue"
                    placeholder="New value"
                    value="${h(O)}"
                    aria-label="New integer value"
                  />
                `:""}

                <button type="submit" class="btn btn-primary">+ Add</button>
              </form>

              <div class="schedule-list-header">
                <span class="panel-meta">${t.length} operation${t.length===1?"":"s"}</span>
                ${t.length>0?'<button type="button" class="link-danger" data-clear-ops>Clear schedule</button>':""}
              </div>

              <ol class="schedule-list">
                ${t.length===0?'<li class="empty-inline">Add operations above to build a schedule.</li>':t.map((n,v)=>{const L=v+1,k=L===b,M=L>b;return`
                    <li class="schedule-row${k?" is-current":""}${M?" is-future":""}" data-select-step="${L}">
                      <span class="step-num">${L}</span>
                      <code class="op-code">${h(n.format())}</code>
                      <span class="row-actions">
                        <button type="button" class="icon-btn" data-move-up="${v}" ${v===0?"disabled":""} title="Move up" aria-label="Move up">↑</button>
                        <button type="button" class="icon-btn" data-move-down="${v}" ${v===t.length-1?"disabled":""} title="Move down" aria-label="Move down">↓</button>
                        <button type="button" class="icon-btn" data-remove-op="${v}" title="Remove operation" aria-label="Remove operation">×</button>
                      </span>
                    </li>
                  `}).join("")}
              </ol>
            `:`
              <p class="panel-hint">
                One operation per line: <code>START T1</code>, <code>READ T1 X</code>,
                <code>WRITE T1 X 12</code>, <code>COMMIT T1</code>, <code>ABORT T2</code>.
              </p>
              <textarea
                class="schedule-textarea"
                rows="8"
                spellcheck="false"
                data-schedule-textarea
                aria-label="Schedule text"
              >${h(o)}</textarea>
              ${a.length>0?`<div class="error-box">
                      <strong>Syntax issues:</strong>
                      <ul>${a.map(n=>`<li>${h(n)}</li>`).join("")}</ul>
                    </div>`:""}
            `}
          </div>
        </div>

        <!-- Step Controls -->
        <div class="step-bar">
          <div class="step-bar-info">
            <span class="step-badge">Step ${b} / ${x}</span>
            <span class="step-label">${h(u.operationLabel)}</span>
          </div>
          <div class="step-bar-controls">
            <button type="button" class="btn btn-secondary btn-sm" data-step-first ${b===0?"disabled":""}>⏮ Start</button>
            <button type="button" class="btn btn-secondary btn-sm" data-step-prev ${b===0?"disabled":""}>← Prev</button>
            <input
              type="range"
              min="0"
              max="${x}"
              value="${b}"
              class="step-slider"
              data-step-slider
              aria-label="Execution step"
            />
            <button type="button" class="btn btn-secondary btn-sm" data-step-next ${b===x?"disabled":""}>Next →</button>
            <button type="button" class="btn btn-secondary btn-sm" data-step-last ${b===x?"disabled":""}>End ⏭</button>
          </div>
        </div>

        ${u.errors.length>0?`
          <div class="error-box">
            <strong>Schedule validation errors (${u.errors.length}):</strong>
            <ul>
              ${u.errors.map(n=>`<li>${h(n)}</li>`).join("")}
            </ul>
          </div>
        `:""}

        <!-- Live Outputs -->
        <div class="outputs-grid">
          <!-- Undo Log -->
          <div class="panel">
            <div class="panel-header">
              <h2>Generated Undo Log</h2>
              <span class="panel-meta">Flushed: ${u.flushedLogLen} / ${u.log.length}</span>
            </div>
            ${u.log.length===0?'<div class="empty-state">No log records emitted yet.</div>':`
              <ol class="log-list">
                ${u.log.map((n,v)=>{const L=v<u.flushedLogLen,k=u.flushedLogLen>0&&v===u.flushedLogLen-1;return`
                    <li class="log-row${L?" is-flushed":" is-unflushed"}">
                      <span class="log-idx">#${v+1}</span>
                      <code class="log-record ${de(n)}">${h(Q(n))}</code>
                      <span class="flush-pill">${L?"on disk":"in log buffer"}</span>
                    </li>
                    ${k?`<li class="flush-divider" aria-hidden="true"><span>↑ flushed to disk (record #${u.flushedLogLen})</span></li>`:""}
                  `}).join("")}
              </ol>
            `}
          </div>

          <!-- Storage & Transactions State -->
          <div class="panel">
            <div class="panel-header">
              <h2>Buffer vs. Disk &amp; Transactions</h2>
              <span class="panel-meta">At step ${b}</span>
            </div>

            <div class="tx-status-group">
              <div class="tx-bucket">
                <span class="tx-bucket-label">Active</span>
                ${u.activeTxs.length===0?'<span class="tx-none">—</span>':u.activeTxs.map(n=>`<span class="tx-pill tx-active">${h(n)}</span>`).join("")}
              </div>
              <div class="tx-bucket">
                <span class="tx-bucket-label">Committed</span>
                ${u.committedTxs.length===0?'<span class="tx-none">—</span>':u.committedTxs.map(n=>`<span class="tx-pill tx-committed">${h(n)}</span>`).join("")}
              </div>
              <div class="tx-bucket">
                <span class="tx-bucket-label">Aborted</span>
                ${u.abortedTxs.length===0?'<span class="tx-none">—</span>':u.abortedTxs.map(n=>`<span class="tx-pill tx-aborted">${h(n)}</span>`).join("")}
              </div>
            </div>

            <table class="state-table">
              <thead>
                <tr>
                  <th>Element</th>
                  <th>Memory Buffer</th>
                  <th>Disk</th>
                  <th>Status</th>
                </tr>
              </thead>
              <tbody>
                ${e.length===0?'<tr><td colspan="4" class="empty-inline">No variables defined.</td></tr>':e.map(n=>{const v=u.buffer[n.name],L=u.disk[n.name],k=v!==L;return`
                    <tr class="${k?"row-dirty":""}">
                      <td><code>${h(n.name)}</code></td>
                      <td><code>${v}</code></td>
                      <td><code>${L}</code></td>
                      <td>
                        <span class="sync-pill ${k?"sync-dirty":"sync-clean"}">
                          ${k?"Dirty (in buffer)":"Synced"}
                        </span>
                      </td>
                    </tr>
                  `}).join("")}
              </tbody>
            </table>
          </div>
        </div>

        <!-- Execution Trace -->
        <div class="panel panel-full">
          <div class="panel-header">
            <h2>Execution Trace (WAL &amp; OUTPUT Ordering)</h2>
            <span class="panel-meta">${u.trace.length} event${u.trace.length===1?"":"s"}</span>
          </div>
          ${u.trace.length===0?'<div class="empty-state">Execute operations to inspect the chronological log, buffer, flush, and disk events.</div>':`
            <ol class="trace-list">
              ${u.trace.map((n,v)=>{const L=ue(n);return`
                  <li class="trace-row${v>=u.newTraceStart&&b>0?" is-new":""}">
                    <span class="trace-idx">${v+1}</span>
                    <span class="trace-tag ${L.cls}">${L.label}</span>
                    <code class="trace-text">${h(re(n).replace(/^[A-Z]+\s+/,""))}</code>
                  </li>
                `}).join("")}
            </ol>
          `}
        </div>

        <!-- Crash Recovery Simulator -->
        <div class="panel panel-full panel-recovery">
          <div class="panel-header">
            <div>
              <h2>Crash Recovery Check</h2>
              <p class="panel-hint">
                Test what <code>UndoRecovery.RecoverFromCrash</code> does if the system crashes
                at <strong>step ${b}</strong> using only the flushed log (records #1–#${u.flushedLogLen}).
              </p>
            </div>
            <button type="button" class="btn btn-secondary" data-simulate-crash>
              Simulate Crash at Step ${b}
            </button>
          </div>

          ${c&&c.stepIndex===b?`
            <div class="recovery-result">
              <div class="recovery-col">
                <h3>Backward Scan Actions</h3>
                ${c.result.actions.length===0?'<p class="panel-hint">No incomplete transactions in the flushed log — disk is already consistent.</p>':`
                  <ul class="recovery-actions">
                    ${c.result.actions.map(n=>n.kind==="RESTORE"?`<li>Restore <code>${h(n.element??"")} := ${n.oldValue}</code> (undo uncommitted <code>${h(n.tx)}</code>)</li>`:`<li>Emit <code>&lt;ABORT ${h(n.tx)}&gt;</code></li>`).join("")}
                  </ul>
                `}
              </div>
              <div class="recovery-col">
                <h3>Recovered Disk State</h3>
                <div class="var-list">
                  ${Object.entries(c.result.recoveredDisk).map(([n,v])=>`
                    <span class="var-chip var-chip-readonly">
                      <span class="var-name">${h(n)}</span>
                      <span class="var-eq">=</span>
                      <code>${v}</code>
                    </span>
                  `).join("")}
                </div>
              </div>
            </div>
          `:""}
        </div>
      </section>
    `,J(u,x)}function J($,u){var n,v,L,k,M,q,F;s.querySelectorAll("[data-preset]").forEach(i=>{i.addEventListener("click",()=>{var y;const p=B.find(A=>A.id===i.dataset.preset);if(!p)return;e=p.variables.map(A=>({...A}));const l=W(p.scheduleText);t=l.operations,o=I(t),a=l.parseErrors,r=null,f="",w=((y=e[0])==null?void 0:y.name)??"X",E(),g()})}),s.querySelectorAll("[data-var-index]").forEach(i=>{i.addEventListener("change",()=>{const p=Number(i.dataset.varIndex),l=Number(i.value);if(!Number.isInteger(l)){i.value=String(e[p].value);return}e[p].value=l,E(),g()})}),s.querySelectorAll("[data-remove-var]").forEach(i=>{i.addEventListener("click",()=>{const p=Number(i.dataset.removeVar);e.splice(p,1),E(),g()})});const x=s.querySelector("[data-add-var-form]");x==null||x.addEventListener("submit",i=>{i.preventDefault();const p=new FormData(x),l=String(p.get("varName")??"").trim(),y=String(p.get("varValue")??"").trim(),A=Number(y);if(!l||/\s/.test(l)){f="Element name must be a non-empty identifier with no spaces.",g();return}if(!Number.isInteger(A)){f="Initial value must be an integer.",g();return}const _=e.find(U=>U.name===l);_?_.value=A:e.push({name:l,value:A}),C="",N="0",f="",E(),g()}),s.querySelectorAll("[data-mode]").forEach(i=>{i.addEventListener("click",()=>{const p=i.dataset.mode;p!==d&&(d=p,p==="text"&&(o=I(t),a=[]),g())})});const b=s.querySelector("[data-add-op-form]");if(b){const i=b.querySelector('select[name="opKind"]'),p=b.querySelector('input[name="opTx"]'),l=b.querySelector('input[name="opElement"]'),y=b.querySelector('input[name="opValue"]');i==null||i.addEventListener("change",()=>{m=i.value,S=(p==null?void 0:p.value)??S,l&&(w=l.value),y&&(O=y.value),g()}),b.addEventListener("submit",A=>{var j;A.preventDefault();const _=((p==null?void 0:p.value)??"").trim()||"T1",U=((l==null?void 0:l.value)??"").trim()||((j=e[0])==null?void 0:j.name)||"X",P=Number((y==null?void 0:y.value)??"0");S=_,w=U,y&&(O=y.value);let D;switch(m){case"START":D=new X(_);break;case"READ":D=new H(_,U);break;case"WRITE":D=new G(_,U,Number.isInteger(P)?P:0);break;case"COMMIT":D=new Y(_);break;case"ABORT":D=new z(_);break}t.push(D),o=I(t),a=[],r=null,E(),g()})}(n=s.querySelector("[data-clear-ops]"))==null||n.addEventListener("click",()=>{t=[],o="",a=[],r=null,E(),g()}),s.querySelectorAll("[data-remove-op]").forEach(i=>{i.addEventListener("click",p=>{p.stopPropagation();const l=Number(i.dataset.removeOp);t.splice(l,1),o=I(t),r=null,E(),g()})}),s.querySelectorAll("[data-move-up]").forEach(i=>{i.addEventListener("click",p=>{p.stopPropagation();const l=Number(i.dataset.moveUp);l<=0||([t[l-1],t[l]]=[t[l],t[l-1]],o=I(t),E(),g())})}),s.querySelectorAll("[data-move-down]").forEach(i=>{i.addEventListener("click",p=>{p.stopPropagation();const l=Number(i.dataset.moveDown);l>=t.length-1||([t[l+1],t[l]]=[t[l],t[l+1]],o=I(t),E(),g())})}),s.querySelectorAll("[data-select-step]").forEach(i=>{i.addEventListener("click",()=>{r=Number(i.dataset.selectStep),E(),g()})});const R=s.querySelector("[data-schedule-textarea]");R==null||R.addEventListener("input",()=>{const i=R.selectionStart,p=R.selectionEnd;o=R.value;const l=W(o);t=l.operations,a=l.parseErrors,r=null,E(),g();const y=s.querySelector("[data-schedule-textarea]");y&&(y.focus(),y.setSelectionRange(i,p))}),(v=s.querySelector("[data-step-first]"))==null||v.addEventListener("click",()=>{r=0,E(),g()}),(L=s.querySelector("[data-step-prev]"))==null||L.addEventListener("click",()=>{r=Math.max(0,$.stepIndex-1),E(),g()}),(k=s.querySelector("[data-step-next]"))==null||k.addEventListener("click",()=>{r=Math.min(u,$.stepIndex+1),E(),g()}),(M=s.querySelector("[data-step-last]"))==null||M.addEventListener("click",()=>{r=null,E(),g()}),(q=s.querySelector("[data-step-slider]"))==null||q.addEventListener("input",i=>{const p=i.target,l=Number(p.value);r=l===u?null:l,E(),g()}),(F=s.querySelector("[data-simulate-crash]"))==null||F.addEventListener("click",()=>{const i=$.log.slice(0,$.flushedLogLen),p={...$.disk},l=ce(p,i);c={stepIndex:$.stepIndex,simulatedDirtyDisk:p,flushedLog:i,result:l},g()})}return g(),s}function he(){return window.location.hash.replace(/^#\/?/,"")==="overview"?"overview":"undo"}function me(s){const e=s==="overview"?"#/overview":"#/logging/undo";window.location.hash!==e&&(window.location.hash=e)}function V(){var r;const s=document.getElementById("app");if(!s)return;const e=he();s.innerHTML="";const t=c=>{me(c),V()},o=document.createElement("div");o.className="mobile-topbar",o.innerHTML=`
    <button type="button" class="btn btn-secondary btn-sm" data-toggle-sidebar aria-label="Toggle navigation">
      ☰ Menu
    </button>
    <span class="mobile-title">DDBB Notes</span>
  `;const a=ne(e,c=>{a.classList.remove("is-open"),t(c)});(r=o.querySelector("[data-toggle-sidebar]"))==null||r.addEventListener("click",()=>{a.classList.toggle("is-open")});const d=document.createElement("main");d.className="blog-main",d.appendChild(e==="overview"?se(t):pe()),s.appendChild(o),s.appendChild(a),s.appendChild(d)}window.addEventListener("hashchange",V);V();
