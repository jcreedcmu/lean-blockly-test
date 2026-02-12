import { useCallback, useEffect, useRef, useState, JSX } from 'react'
import * as React from 'react'
import Split from 'react-split'
import * as monaco from 'monaco-editor'
import CodeMirror, { EditorView } from '@uiw/react-codemirror'
import { LeanMonaco, LeanMonacoEditor, LeanMonacoOptions } from 'lean4monaco'
import LZString from 'lz-string'
import { FontAwesomeIcon } from '@fortawesome/react-fontawesome'
import { faCode } from '@fortawesome/free-solid-svg-icons'
import * as path from 'path'

// Local imports
import LeanLogo from './assets/logo.svg'
import defaultSettings, { IPreferencesContext, lightThemes, preferenceParams } from './config/settings'
import { Menu } from './Navigation'
import { PreferencesContext } from './Popups/Settings'
import { Entries } from './utils/Entries'
import { save } from './utils/SaveToFile'
import { fixedEncodeURIComponent, formatArgs, lookupUrl, parseArgs } from './utils/UrlParsing'
import { useWindowDimensions } from './utils/WindowWidth'
import { Blockly, BlocklyHandle, BlocklyState } from './Blockly.tsx';
import type { WorkspaceToLeanResult, SourceInfo } from './workspaceToLean';
import { Goals } from './infoview';
import './infoview/infoview.css';
import type { InteractiveGoals } from '@leanprover/infoview-api';
import { connect as lspConnect } from './LeanLspClient';
import { LeanRpcSession } from './LeanRpcSession';
import { example as example1 } from './examples/example-1.ts';
import { example as example2 } from './examples/example-2.ts';
import { example as example3 } from './examples/example-3.ts';
import { example as example4 } from './examples/example-4.ts';

type LevelDefinition = {
  name: string;
  initial: BlocklyState;
  allowedBlocks?: string[];  // If undefined, all blocks are available
};

const levelDefinitions: LevelDefinition[] = [
  {
    name: "Use Hypothesis",
    initial: example1,
    allowedBlocks: ['tactic_apply', 'prop'],
  },
  {
    name: "Reflexivity",
    initial: example2,
    allowedBlocks: ['tactic_refl'],
  },
  {
    name: "Rewrite",
    initial: example3,
    allowedBlocks: ['tactic_rw', 'prop'],
  },
  {
    name: "Limit Example",
    initial: example4,
  },
];

// CSS
import './css/App.css'
import './css/Editor.css'

/** Returns true if the browser wants dark mode */
function isBrowserDefaultDark() {
  return window.matchMedia('(prefers-color-scheme: dark)').matches
}

function Wrapp(props: {
  editor: monaco.editor.IStandaloneCodeEditor,
  setEditor: (e: monaco.editor.IStandaloneCodeEditor) => void,
}) {
  const { editor, setEditor } = props;
  const editorRef = useRef<HTMLDivElement>(null)
  const infoviewRef = useRef<HTMLDivElement>(null)
  const [dragging, setDragging] = useState<boolean | null>(false)
  const [leanMonaco, setLeanMonaco] = useState<LeanMonaco>()
  const [loaded, setLoaded] = useState<boolean>(false)
  const [preferences, setPreferences] = useState<IPreferencesContext>(defaultSettings)
  const { width } = useWindowDimensions()


  // Lean4monaco options
  const [options, setOptions] = useState<LeanMonacoOptions>({
    // placeholder, updated below
    websocket: { url: '' }
  })

  // Because of Monaco's missing mobile support we add a codeMirror editor
  // which can be enabled to do editing.
  // TODO: It would be nice to integrate Lean into CodeMirror better.
  // first step could be to pass the cursor selection to the underlying monaco editor
  const [codeMirror, setCodeMirror] = useState(false)

  // the user data
  const [code, setCode] = useState<string>('')
  const [project, setProject] = useState<string>(undefined)
  const [url, setUrl] = useState<string | null>(null)
  const [codeFromUrl, setCodeFromUrl] = useState<string>('')

  /** Monaco editor requires the code to be set manually. */
  function setContent(code: string) {
    editor?.getModel()?.setValue(code)
    setCode(code)
  }

  // Read the URL arguments
  useEffect(() => {
    // Parse args
    console.log('[Lean4web] Parsing URL')
    let args = parseArgs()
    if (args.code) {
      let _code = decodeURIComponent(args.code)
      setContent(_code)
    } else if (args.codez) {
      let _code = LZString.decompressFromBase64(args.codez)
      setContent(_code)
    }

    if (args.url) { setUrl(lookupUrl(decodeURIComponent(args.url))) }

    // if no project provided, use default
    let project = args.project || 'MathlibDemo'

    console.log(`[Lean4web] Setting project to ${project}`)
    setProject(project)
  }, [])

  // Load preferences from store in the beginning
  useEffect(() => {
    // only load them once
    if (loaded) { return }
    console.debug('[Lean4web] Loading preferences')

    let saveInLocalStore = false;
    let newPreferences: { [K in keyof IPreferencesContext]: IPreferencesContext[K] } = { ...preferences }
    for (const [key, value] of (Object.entries(preferences) as Entries<IPreferencesContext>)) {
      // prefer URL params over stored
      const searchParams = new URLSearchParams(window.location.search);
      let storedValue = (
        preferenceParams.includes(key) &&  // only for keys we explictly check for
        searchParams.has(key) && searchParams.get(key))
        ?? window.localStorage.getItem(key)
      if (storedValue) {
        saveInLocalStore = window.localStorage.getItem(key) === storedValue
        console.debug(`[Lean4web] Found value for ${key}: ${storedValue}`)
        if (typeof value === 'string') {
          if (key == 'theme') {
            const theme = storedValue.toLowerCase().includes('dark') ? "Visual Studio Dark" : "Visual Studio Light"
            newPreferences[key] = theme
          }
          else {
            newPreferences[key] = storedValue
          }
        } else if (typeof value === 'boolean') {
          newPreferences[key] = (storedValue === "true")
        } else {
          // other values aren't implemented yet.
          console.error(`[Lean4web] Preferences (key: ${key}) contain a value of unsupported type: ${typeof value}`)
        }
      } else {
        // no stored preferences, set a default value
        if (key == 'theme') {
          if (isBrowserDefaultDark()) {
            console.debug("[Lean4web] Preferences: Set dark theme.")
            newPreferences['theme'] = 'Visual Studio Dark'
          } else {
            console.debug("[Lean4web] Preferences: Set light theme.")
            newPreferences['theme'] = 'Visual Studio Light'
          }
        }
      }
    }
    newPreferences['saveInLocalStore'] = saveInLocalStore
    setPreferences(newPreferences)
    setLoaded(true)
  }, [])

  // Use the window width to switch between mobile/desktop layout
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }

    const _mobile = width < 800
    const searchParams = new URLSearchParams(window.location.search);
    if (!(searchParams.has("mobile") || preferences.saveInLocalStore) && _mobile !== preferences.mobile) {
      setPreferences({ ...preferences, mobile: _mobile })
    }
  }, [width, loaded])

  // Update LeanMonaco options when preferences are loaded or change
  useEffect(() => {
    if (!project) { return }
    console.log('[Lean4web] Update lean4monaco options')

    var socketUrl = ((window.location.protocol === "https:") ? "wss://" : "ws://") +
      window.location.host + "/websocket/" + project
    console.log(`[Lean4web] Socket url is ${socketUrl}`)
    var _options: LeanMonacoOptions = {
      websocket: { url: socketUrl },
      // Restrict monaco's extend (e.g. context menu) to the editor itself
      htmlElement: editorRef.current ?? undefined,
      vscode: {
        /* To add settings here, you can open your settings in VSCode (Ctrl+,), search
         * for the desired setting, select "Copy Setting as JSON" from the "More Actions"
         * menu next to the selected setting, and paste the copied string here.
         */
        "workbench.colorTheme": preferences.theme,
        "editor.tabSize": 2,
        // "editor.rulers": [100],
        "editor.lightbulb.enabled": "on",
        "editor.wordWrap": preferences.wordWrap ? "on" : "off",
        "editor.wrappingStrategy": "advanced",
        "editor.semanticHighlighting.enabled": true,
        "editor.acceptSuggestionOnEnter": preferences.acceptSuggestionOnEnter ? "on" : "off",
        "lean4.input.eagerReplacementEnabled": true,
        "lean4.infoview.showGoalNames": preferences.showGoalNames,
        "lean4.infoview.emphasizeFirstGoal": true,
        "lean4.infoview.showExpectedType": false,
        "lean4.infoview.showTooltipOnHover": false,
        "lean4.input.leader": preferences.abbreviationCharacter
      }
    }
    setOptions(_options)
  }, [editorRef, project, preferences])

  // Setting up the editor and infoview
  useEffect(() => {
    // Wait for preferences to be loaded
    if (!loaded) { return }
    console.debug('[Lean4web] Restarting editor')
    var _leanMonaco = new LeanMonaco()
    var leanMonacoEditor = new LeanMonacoEditor()

    _leanMonaco.setInfoviewElement(infoviewRef.current!)
      ; (async () => {
        await _leanMonaco.start(options)
        await leanMonacoEditor.start(editorRef.current!, path.join(project, `${project}.lean`), code)

        setEditor(leanMonacoEditor.editor)
        setLeanMonaco(_leanMonaco)

        // Add a `Paste` option to the context menu on mobile.
        // Monaco does not support clipboard pasting as all browsers block it
        // due to security reasons. Therefore we use a codeMirror editor overlay
        // which features good mobile support (but no Lean support yet)
        if (preferences.mobile) {
          leanMonacoEditor.editor?.addAction({
            id: "myPaste",
            label: "Paste: open 'Plain Editor' for editing on mobile",
            // keybindings: [monaco.KeyMod.CtrlCmd | monaco.KeyCode.KEY_V],
            contextMenuGroupId: "9_cutcopypaste",
            run: (_editor) => {
              setCodeMirror(true)
            }
          })
        }

        // // TODO: This was an approach to create a new definition provider, but it
        // // wasn't that useful. I'll leave it here in connection with the TODO below for
        // // reference.
        // monaco.languages.registerDefinitionProvider('lean4', {
        //   provideDefinition(model, position) {
        //     const word = model.getWordAtPosition(position);
        //     if (word) {
        //       console.log(`[Lean4web] Providing definition for: ${word.word}`);
        //       // Return the location of the definition
        //       return [
        //         {
        //           uri: model.uri,
        //           range: {startLineNumber: 0, startColumn: word.startColumn, endColumn: word.endColumn, endLineNumber: 0}, // Replace with actual definition range
        //         },
        //       ];
        //     }
        //     return null;
        //   },
        // });

        // TODO: Implement Go-To-Definition better
        // This approach only gives us the file on the server (plus line number) it wants
        // to open, is there a better approach?
        const editorService = (leanMonacoEditor.editor as any)?._codeEditorService
        if (editorService) {
          const openEditorBase = editorService.openCodeEditor.bind(editorService)
          editorService.openCodeEditor = async (input: any, source: any) => {
            const result = await openEditorBase(input, source)
            if (result === null) {
              // found this out with `console.debug(input)`:
              // `resource.path` is the file go-to-def tries to open on the disk
              // we try to create a doc-gen link from that. Could not extract the
              // (fully-qualified) decalaration name... with that one could
              // call `...${path}.html#${declaration}`
              let path = input.resource.path.replace(
                new RegExp("^.*/(?:lean|\.lake/packages/[^/]+/)"), ""
              ).replace(
                new RegExp("\.lean$"), ""
              )

              if (window.confirm(`Do you want to open the docs?\n\n${path} (line ${input.options.selection.startLineNumber})`)) {
                let newTab = window.open(`https://leanprover-community.github.io/mathlib4_docs/${path}.html`, "_blank")
                if (newTab) {
                  newTab.focus()
                }
              }
            }
            return null
            // return result // always return the base result
          }
        }

        // Keeping the `code` state up-to-date with the changes in the editor
        leanMonacoEditor.editor?.onDidChangeModelContent(() => {
          setCode(leanMonacoEditor.editor?.getModel()?.getValue()!)
        })
      })()
    return () => {
      leanMonacoEditor.dispose()
      _leanMonaco.dispose()
    }
  }, [loaded, project, preferences, options, infoviewRef, editorRef])

  // Load content from source URL.
  // Once the editor is loaded, this reads the content of any provided `url=` in the URL and
  // saves this content as `codeFromURL`. It is important that we only do this once
  // the editor is loaded, as the `useEffect` below only triggers when the `codeFromURL`
  // changes, otherwise it might overwrite local changes too often.
  useEffect(() => {
    if (!editor || !url) { return }
    console.debug(`[Lean4web] Loading from ${url}`)
    fetch(url)
      .then((response) => response.text())
      .then((code) => {
        setCodeFromUrl(code)
      })
      .catch(err => {
        let errorTxt = `ERROR: ${err.toString()}`
        console.error(errorTxt)
        setCodeFromUrl(errorTxt)
      })
  }, [url, editor])

  // Sets the editors content to the content from the loaded URL.
  // As described above, this requires the editor is loaded, but we do not want to
  // trigger this effect every time the editor is reloaded (e.g. config change) as otherwise
  // we would constantly overwrite the user's local changes
  useEffect(() => {
    if (!codeFromUrl) { return }
    setContent(codeFromUrl)
  }, [codeFromUrl])

  // Keep the URL updated on change
  useEffect(() => {
    if (!editor) { return }

    let _project = (project == 'MathlibDemo' ? null : project)
    let args: {
      project: string | null
      url: string | null
      code: string | null
      codez: string | null
    }
    if (code === "") {
      args = {
        project: _project,
        url: null,
        code: null,
        codez: null
      }
    } else if (url != null && code == codeFromUrl) {
      args = {
        project: _project,
        url: encodeURIComponent(url),
        code: null,
        codez: null
      }
    } else if (preferences.compress) {
      // LZ padds the string with trailing `=`, which mess up the argument parsing
      // and aren't needed for LZ encoding, so we remove them.
      const compressed = LZString.compressToBase64(code).replace(/=*$/, '')
      // // Note: probably temporary; might be worth to always compress as with whitespace encoding
      // // it needs very little for the compressed version to be shorter
      // const encodedCode = fixedEncodeURIComponent(code)
      // console.debug(`[Lean4web] Code length: ${encodedCode.length}, compressed: ${compressed.length}`)
      // if (compressed.length < encodedCode.length) {
      args = {
        project: _project,
        url: null,
        code: null,
        codez: compressed
      }
      // } else {
      //   args = {
      //     project: _project,
      //     url: null,
      //     code: encodedCode,
      //     codez: null
      //   }
      // }
    } else {
      args = {
        project: _project,
        url: null,
        code: fixedEncodeURIComponent(code),
        codez: null
      }
    }
    history.replaceState(undefined, undefined!, formatArgs(args))
  }, [editor, project, code, codeFromUrl])

  // Disable monaco context menu outside the editor
  useEffect(() => {
    const handleContextMenu = (event: MouseEvent) => {
      const editorContainer = document.querySelector(".editor")
      // Always prevent default context menu
      event.preventDefault();
      if (editorContainer && !editorContainer.contains(event.target as Node)) {
        event.stopPropagation();
      }
    }
    document.addEventListener("contextmenu", handleContextMenu, true)
    return () => {
      document.removeEventListener("contextmenu", handleContextMenu, true)
    }
  }, [])

  // Stop the browser's save dialog on Ctrl+S
  const handleKeyDown = useCallback((event: KeyboardEvent) => {
    if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 's') {
      event.preventDefault()
    }
  }, [])

  // Actually save the file on Ctrl+S
  const handleKeyUp = useCallback((event: KeyboardEvent) => {
    if ((event.ctrlKey || event.metaKey) && event.key.toLowerCase() === 's') {
      event.preventDefault()
      save(code)
    }
  }, [code])

  useEffect(() => {
    document.addEventListener('keydown', handleKeyDown)
    document.addEventListener('keyup', handleKeyUp)
    return () => {
      document.removeEventListener('keydown', handleKeyDown)
      document.removeEventListener('keyup', handleKeyUp)
    }
  }, [handleKeyDown, handleKeyUp])

  return <PreferencesContext.Provider value={{ preferences, setPreferences }}>
    <div className="app monaco-editor">
      <nav>
        <LeanLogo />
        <Menu
          code={code}
          setContent={setContent}
          project={project}
          setProject={setProject}
          setUrl={setUrl}
          codeFromUrl={codeFromUrl}
          restart={leanMonaco?.restart}
          codeMirror={codeMirror}
          setCodeMirror={setCodeMirror}
        />
      </nav>
      <Split className={`editor ${dragging ? 'dragging' : ''}`}
        gutter={(_index, _direction) => {
          const gutter = document.createElement('div')
          gutter.className = `gutter` // no `gutter-${direction}` as it might change
          return gutter
        }}
        gutterStyle={(_dimension, gutterSize, _index) => {
          return {
            'width': preferences.mobile ? '100%' : `${gutterSize}px`,
            'height': preferences.mobile ? `${gutterSize}px` : '100%',
            'cursor': preferences.mobile ? 'row-resize' : 'col-resize',
            'margin-left': preferences.mobile ? 0 : `-${gutterSize}px`,
            'margin-top': preferences.mobile ? `-${gutterSize}px` : 0,
            'z-index': 0,
          }
        }}
        gutterSize={5}
        onDragStart={() => setDragging(true)} onDragEnd={() => setDragging(false)}
        sizes={preferences.mobile ? [50, 50] : [70, 30]}
        direction={preferences.mobile ? "vertical" : "horizontal"}
        style={{ flexDirection: preferences.mobile ? "column" : "row" }}>
        <div className='codeview-wrapper'
          style={preferences.mobile ? { width: '100%' } : { height: '100%' }} >
          {codeMirror &&
            <CodeMirror
              className="codeview plain"
              value={code}
              extensions={[EditorView.lineWrapping]}
              height='100%'
              maxHeight='100%'
              theme={lightThemes.includes(preferences.theme) ? 'light' : 'dark'}
              onChange={setContent} />
          }
          <div ref={editorRef} className={`codeview${codeMirror ? ' hidden' : ''}`} />
        </div>
        <div ref={infoviewRef} className="vscode-light infoview"
          style={preferences.mobile ? { width: '100%' } : { height: '100%' }} >
          <p className={`editor-support-warning${codeMirror ? '' : ' hidden'}`} >
            You are in the plain text editor<br /><br />
            Go back to the Monaco Editor (click <FontAwesomeIcon icon={faCode} />)
            for the infoview to update!
          </p>
        </div>
      </Split>
    </div>
  </PreferencesContext.Provider>

}

// Virtual document URI for Blockly code
const BLOCKLY_DOC_URI = 'file:///blockly/Blockly.lean';

function App() {
  const [show, setShow] = useState(true);
  const [goals, setGoals] = useState<InteractiveGoals | null>(null);
  const [goalsLoading, setGoalsLoading] = useState(false);
  const [proofComplete, setProofComplete] = useState<boolean | null>(null); // null = checking, true = complete, false = incomplete
  const [editor, setEditor] = useState<monaco.editor.IStandaloneCodeEditor>()
  const blocklyRef = useRef<BlocklyHandle>(null);
  const [currentLevelIndex, setCurrentLevelIndex] = useState(0);
  const [levelStates, setLevelStates] = useState<BlocklyState[]>(
    () => levelDefinitions.map(ex => ex.initial)
  );

  // RPC session for Blockly code
  const rpcSessionRef = useRef<LeanRpcSession | null>(null);
  const [rpcManagerReady, setRpcManagerReady] = useState(false);

  // Track latest goals for proof status updates
  const latestGoalsRef = useRef<InteractiveGoals | null>(null);

  // Function to update proof status based on current goals and diagnostics
  const updateProofStatus = useCallback(() => {
    if (!rpcSessionRef.current) return;

    const hasErrors = rpcSessionRef.current.hasErrors();
    const diagnostics = rpcSessionRef.current.getDiagnostics();
    const currentGoals = latestGoalsRef.current;

    console.log('[updateProofStatus] Has errors:', hasErrors, 'Goals:', currentGoals?.goals?.length ?? 'null');
    console.log('[updateProofStatus] Diagnostics:', diagnostics);

    // Don't update status if we don't have goals data yet (still checking)
    if (currentGoals === null) return;

    // Proof is complete only if there are no goals AND no errors
    const noGoals = currentGoals.goals.length === 0;
    const isComplete = noGoals && !hasErrors;
    setProofComplete(isComplete);
  }, []);

  // Initialize standalone LSP connection + RPC session
  useEffect(() => {
    let disposed = false;

    const wsProto = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
    const wsUrl = `${wsProto}//${window.location.host}/websocket/MathlibDemo`;

    lspConnect(wsUrl).then((conn) => {
      if (disposed) { conn.dispose(); return; }

      const session = new LeanRpcSession(conn, BLOCKLY_DOC_URI);
      rpcSessionRef.current = session;

      session.setDiagnosticsCallback((diagnostics) => {
        console.log('[App] Diagnostics changed:', diagnostics.length, 'items');
        updateProofStatus();
      });

      setRpcManagerReady(true);
      console.log('[App] LeanRpcSession ready');
    }).catch((err) => {
      console.error('[App] LSP connection failed:', err);
    });

    return () => {
      disposed = true;
      rpcSessionRef.current?.dispose();
      rpcSessionRef.current = null;
      setRpcManagerReady(false);
    };
  }, [updateProofStatus]);

  function switchToLevel(newIndex: number) {
    if (newIndex === currentLevelIndex) return;

    // Save current workspace state
    const currentState = blocklyRef.current?.saveWorkspace();
    if (currentState) {
      setLevelStates(prev => {
        const updated = [...prev];
        updated[currentLevelIndex] = currentState;
        return updated;
      });
    }

    // Load the new level
    blocklyRef.current?.loadWorkspace(levelStates[newIndex]);
    setCurrentLevelIndex(newIndex);
  }

  function resetCurrentLevel() {
    const initialState = levelDefinitions[currentLevelIndex].initial;
    blocklyRef.current?.loadWorkspace(initialState);
    setLevelStates(prev => {
      const updated = [...prev];
      updated[currentLevelIndex] = initialState;
      return updated;
    });
  }

  function injectClick(s: string, p: monaco.IPosition) {
    const model = editor.getModel();
    model.setValue(s);
    editor.setPosition(p);
    // editor.focus();
  }

  function focusClick() {
    editor.focus();
  }

  const [dragging, setDragging] = useState(false);

  const myStyle: React.CSSProperties = {
    position: 'absolute',
    top: 0, left: 0, right: 0, bottom: 0,
    overflow: 'hidden',
  };
  const kid1: React.CSSProperties = {
    display: 'flex',
    flexDirection: 'row',
    overflow: 'hidden',
  };
  const blocklyContainer: React.CSSProperties = {
    flexGrow: 1,
  };
  function changeChecked(e: React.ChangeEvent) {
    setShow((e.currentTarget as HTMLInputElement).checked);
  }
  function onBlocklyChange(result: WorkspaceToLeanResult) {
    const { leanCode } = result;
    const fullCode = prelude + leanCode;

    // Update Monaco editor (for debugging/viewing)
    editor?.getModel()?.setValue(fullCode);

    // Check proof status by fetching goals for the entire file
    if (rpcSessionRef.current) {
      setProofComplete(null); // Set to "checking" state

      console.log('[onBlocklyChange] Fetching goals for file');

      (async () => {
        try {
          const goals = await rpcSessionRef.current!.getGoals(fullCode);
          console.log('[onBlocklyChange] Goals:', goals);

          // Store goals for later reference (diagnostics callback can update status)
          latestGoalsRef.current = goals;

          // Also update displayed goals
          setGoals(goals);

          // Update proof status based on current goals and diagnostics
          updateProofStatus();
        } catch (err) {
          console.error('[onBlocklyChange] Error checking proof status:', err);
          setProofComplete(false);
        }
      })();
    }
  }

  const prelude = `import Mathlib

def FunLimAt (f : ℝ → ℝ) (L : ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε

`;

  async function onRequestGoals(
    blockId: string,
    leanCode: string,
    _sourceInfo: SourceInfo[],
    _blockSourceInfo: SourceInfo | undefined
  ) {
    console.log('[onRequestGoals] ========================================');
    console.log('[onRequestGoals] Block ID:', blockId);

    if (!rpcSessionRef.current) {
      console.log('[onRequestGoals] RPC session not initialized');
      return;
    }

    const fullCode = prelude + leanCode;
    console.log('[onRequestGoals] Full code being sent:');
    console.log('---BEGIN CODE---');
    console.log(fullCode);
    console.log('---END CODE---');

    setGoalsLoading(true);
    try {
      console.log('[onRequestGoals] Fetching goals via LeanRpcSession...');
      const goals = await rpcSessionRef.current.getGoals(fullCode);
      console.log('[onRequestGoals] Goals received:', goals);

      if (goals) {
        console.log('[onRequestGoals] Setting goals');
        setGoals(goals);
      } else {
        console.log('[onRequestGoals] No goals returned');
      }
    } catch (err) {
      console.error('[onRequestGoals] Error fetching goals:', err);
    } finally {
      setGoalsLoading(false);
    }
  }

  return <div style={myStyle}>
    <Split
      className={dragging ? 'dragging' : ''}
      direction="vertical"
      sizes={[60, 40]}
      minSize={100}
      gutterSize={5}
      onDragStart={() => setDragging(true)}
      onDragEnd={() => setDragging(false)}
      style={{ display: 'flex', flexDirection: 'column', height: '100%' }}
      gutter={() => {
        const gutter = document.createElement('div');
        gutter.className = 'gutter gutter-vertical';
        return gutter;
      }}
      gutterStyle={() => ({
        height: '5px',
        backgroundColor: '#ccc',
      })}
    >
      <div style={kid1}>
        <div className="buttons">
          {levelDefinitions.map((ex, i) => (
            <button
              key={i}
              onClick={() => switchToLevel(i)}
              style={{ fontWeight: i === currentLevelIndex ? 'bold' : 'normal' }}
            >
              {i + 1}
            </button>
          ))}
          <button onClick={resetCurrentLevel}>Reset</button>
          <button onClick={() => {
            const state = blocklyRef.current?.saveWorkspace();
            if (state) {
              navigator.clipboard.writeText(JSON.stringify(state, null, 2));
              console.log('Workspace copied to clipboard');
            }
          }}>Copy</button>
        </div>
        <Blockly
          ref={blocklyRef}
          style={blocklyContainer}
          onBlocklyChange={onBlocklyChange}
          onRequestGoals={onRequestGoals}
          initialData={levelDefinitions[0].initial}
          allowedBlocks={levelDefinitions[currentLevelIndex].allowedBlocks}
        />
        <div style={{ width: '300px', padding: '0.5em', borderLeft: '1px solid #ccc', overflow: 'auto' }}>
          <div className="proof-status">
            {proofComplete === null ? (
              <span className="proof-checking">Checking...</span>
            ) : proofComplete ? (
              <span className="proof-complete">✓ Proof complete!</span>
            ) : (
              <span className="proof-incomplete">Proof incomplete</span>
            )}
          </div>
          {goalsLoading ? (
            <div className="goals-loading">
              <div className="spinner" />
              <span>Loading goals...</span>
            </div>
          ) : (
            <Goals goals={goals} />
          )}
        </div>
      </div>
      <div style={{ overflow: 'hidden' }}>{show ? <Wrapp editor={editor} setEditor={setEditor} /> : undefined}</div>
    </Split>
  </div>;
}

/* var selection = editor.getSelection();
 * var id = { major: 1, minor: 1 };
 * var text = "XXX";
 * var op = {identifier: id, range: selection, text: text, forceMoveMarkers: true};
 * editor.executeEdits("my-source", [op]); */
export default App
