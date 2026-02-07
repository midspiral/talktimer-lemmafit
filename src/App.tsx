import { useState, useEffect, useCallback, useRef } from 'react'
import Api, { Action, Lap } from './dafny/app'
import './App.css'

type DafnyHistory = ReturnType<typeof Api.InitHistory>

// Format milliseconds as MM:SS
function formatTime(ms: number): string {
  const totalSeconds = Math.floor(ms / 1000)
  const minutes = Math.floor(totalSeconds / 60)
  const seconds = totalSeconds % 60
  return `${minutes.toString().padStart(2, '0')}:${seconds.toString().padStart(2, '0')}`
}

// Parse MM:SS or M:SS or SS to milliseconds
function parseTime(str: string): number | null {
  const trimmed = str.trim()
  const parts = trimmed.split(':')
  if (parts.length === 1) {
    // Just seconds
    const secs = parseInt(parts[0], 10)
    if (isNaN(secs) || secs < 0) return null
    return secs * 1000
  } else if (parts.length === 2) {
    // MM:SS
    const mins = parseInt(parts[0], 10)
    const secs = parseInt(parts[1], 10)
    if (isNaN(mins) || isNaN(secs) || mins < 0 || secs < 0 || secs >= 60) return null
    return (mins * 60 + secs) * 1000
  }
  return null
}

// Compute total duration of selected takes
function getSelectedTotal(laps: Lap[]): number {
  return laps.filter(lap => lap.selected).reduce((sum, lap) => sum + lap.duration, 0)
}

// Count selected laps
function getSelectedCount(laps: Lap[]): number {
  return laps.filter(lap => lap.selected).length
}

// Compute totals by tag for selected laps
function getTagTotals(laps: Lap[]): { tag: string; total: number; count: number }[] {
  const tagMap = new Map<string, { total: number; count: number }>()

  for (const lap of laps) {
    if (!lap.selected) continue
    for (const tag of lap.tags) {
      const existing = tagMap.get(tag) || { total: 0, count: 0 }
      tagMap.set(tag, { total: existing.total + lap.duration, count: existing.count + 1 })
    }
  }

  return Array.from(tagMap.entries())
    .map(([tag, data]) => ({ tag, ...data }))
    .sort((a, b) => b.total - a.total)
}

// Generate markdown export of selected laps
function generateMarkdown(laps: Lap[]): string {
  const lines = laps
    .filter(lap => lap.selected)
    .map(lap => {
      const label = lap.section || 'Untitled'
      const tagsStr = lap.tags.length > 0 ? ` [${lap.tags.join(', ')}]` : ''
      return `- [ ] ${label}${tagsStr} (${formatTime(lap.duration)})`
    })
  lines.push(`- [ ] Total (${formatTime(getSelectedTotal(laps))})`)
  return lines.join('\n')
}

// Parse markdown import format: "- [ ] Label [tag1, tag2] (MM:SS)" or "- [ ] Label (MM:SS)"
function parseMarkdown(text: string): { section: string; duration: number; tags: string[] }[] {
  const lines = text.split('\n')
  const results: { section: string; duration: number; tags: string[] }[] = []

  for (const line of lines) {
    // Match "- [ ] Label [tags] (MM:SS)" or "- [ ] Label (MM:SS)"
    const match = line.match(/^-\s*\[.\]\s*(.+?)\s*\((\d+:\d+)\)\s*$/)
    if (match) {
      let labelPart = match[1].trim()
      // Skip the Total line
      if (labelPart.toLowerCase() === 'total') continue

      // Extract tags if present: "Label [tag1, tag2]" -> section="Label", tags=["tag1", "tag2"]
      let tags: string[] = []
      const tagMatch = labelPart.match(/^(.+?)\s*\[([^\]]+)\]$/)
      if (tagMatch) {
        labelPart = tagMatch[1].trim()
        tags = tagMatch[2].split(',').map(t => t.trim()).filter(t => t.length > 0)
      }

      const duration = parseTime(match[2])
      if (duration !== null) {
        results.push({ section: labelPart, duration, tags })
      }
    }
  }
  return results
}

function App() {
  // Timer state
  const [running, setRunning] = useState(false)
  const [startTime, setStartTime] = useState<number | null>(null)
  const [displayTime, setDisplayTime] = useState(0)

  // Model state with history for undo/redo (using verified Dafny history)
  const [dafnyHistory, setDafnyHistory] = useState(() => Api.InitHistory())

  // Editing state
  const [editingLap, setEditingLap] = useState<number | null>(null)
  const [editingDuration, setEditingDuration] = useState<number | null>(null)
  const [editingTagsIdx, setEditingTagsIdx] = useState<number | null>(null)
  const [editText, setEditText] = useState('')
  const [editDurationText, setEditDurationText] = useState('')
  const [newTagText, setNewTagText] = useState('')
  const sectionInputRef = useRef<HTMLInputElement>(null)
  const durationInputRef = useRef<HTMLInputElement>(null)
  const tagInputRef = useRef<HTMLInputElement>(null)


  // Convert Dafny history to JSON for rendering
  const history = Api.historyToJson(dafnyHistory)
  const model = history.present
  const canUndo = history.past.length > 0
  const canRedo = history.future.length > 0

  // Apply action with history tracking
  const dispatch = useCallback((action: Action) => {
    setDafnyHistory((h: DafnyHistory) => {
      const dafnyAction = Api.actionFromJson(action)
      return Api.Do(h, dafnyAction)
    })
  }, [])

  // Undo
  const undo = useCallback(() => {
    setDafnyHistory((h: DafnyHistory) => Api.Undo(h))
  }, [])

  // Redo
  const redo = useCallback(() => {
    setDafnyHistory((h: DafnyHistory) => Api.Redo(h))
  }, [])

  // Timer effect
  useEffect(() => {
    if (!running || startTime === null) return

    const interval = setInterval(() => {
      const elapsed = Date.now() - startTime
      setDisplayTime(elapsed)
    }, 100)

    return () => clearInterval(interval)
  }, [running, startTime])

  // Start/stop timer
  const toggleTimer = () => {
    if (running) {
      setRunning(false)
    } else {
      if (startTime === null) {
        setStartTime(Date.now())
      } else {
        setStartTime(Date.now() - displayTime)
      }
      setRunning(true)
    }
  }

  // Reset timer (undoable)
  const resetTimer = () => {
    setRunning(false)
    setStartTime(null)
    setDisplayTime(0)
    dispatch({ type: 'Reset' })
  }

  // Start practice mode - use current laps as template
  const startPractice = () => {
    const labels = model.laps
      .filter(lap => lap.section !== '')
      .map(lap => ({ section: lap.section, expectedDuration: lap.duration, tags: lap.tags }))
    if (labels.length === 0) return
    setRunning(false)
    setStartTime(null)
    setDisplayTime(0)
    // Set template then reset (template survives reset? No - reset clears it)
    // We need to set template AFTER reset, so do it in one setDafnyHistory call
    setDafnyHistory((h: DafnyHistory) => {
      const resetAction = Api.actionFromJson({ type: 'Reset' })
      const h1 = Api.Do(h, resetAction)
      const setTemplateAction = Api.actionFromJson({ type: 'SetTemplate', labels })
      return Api.Do(h1, setTemplateAction)
    })
  }

  // Create lap at current time
  const createLap = () => {
    setDafnyHistory((h: DafnyHistory) => {
      const setTimeAction = Api.actionFromJson({ type: 'SetTime', ms: displayTime })
      const createLapAction = Api.actionFromJson({ type: 'CreateLap' })

      const h1 = Api.Do(h, setTimeAction)
      const h2 = Api.Do(h1, createLapAction)

      // In practice mode, auto-label from template
      if (model.template.length > 0) {
        const consumeAction = Api.actionFromJson({ type: 'ConsumeTemplate' })
        return Api.Do(h2, consumeAction)
      }

      return h2
    })
  }

  // Label a lap
  const labelLap = (idx: number, name: string) => {
    dispatch({ type: 'LabelLap', idx, name })
    setEditingLap(null)
  }

  // Adjust duration
  const adjustDuration = (idx: number, durationStr: string) => {
    const duration = parseTime(durationStr)
    if (duration !== null) {
      dispatch({ type: 'AdjustDuration', idx, duration })
    }
    setEditingDuration(null)
  }

  // Toggle lap selection
  const toggleSelect = (idx: number) => {
    dispatch({ type: 'SelectLap', idx })
  }

  // Delete a lap
  const deleteLap = (idx: number) => {
    dispatch({ type: 'DeleteLap', idx })
  }

  // Move lap up
  const moveUp = (idx: number) => {
    dispatch({ type: 'MoveUp', idx })
  }

  // Move lap down
  const moveDown = (idx: number) => {
    dispatch({ type: 'MoveDown', idx })
  }

  // Add tag to lap
  const addTag = (idx: number, tag: string) => {
    const trimmedTag = tag.trim()
    if (trimmedTag) {
      dispatch({ type: 'AddTag', idx, tag: trimmedTag })
    }
    setNewTagText('')
    setEditingTagsIdx(null)
  }

  // Remove tag from lap
  const removeTag = (idx: number, tag: string) => {
    dispatch({ type: 'RemoveTag', idx, tag })
  }

  // Start editing tags for a lap
  const startEditingTags = (idx: number) => {
    setEditingTagsIdx(idx)
    setEditingLap(null)
    setEditingDuration(null)
    setNewTagText('')
    setTimeout(() => tagInputRef.current?.focus(), 0)
  }

  // Import from markdown (paste)
  const importMarkdown = async () => {
    const text = await navigator.clipboard.readText()
    const parsed = parseMarkdown(text)
    if (parsed.length === 0) return

    // Create lap objects for import
    const laps = parsed.map(({ section, duration, tags }) => ({
      timestamp: 0,
      duration,
      section,
      selected: true,
      expectedDuration: -1,
      tags
    }))

    dispatch({ type: 'ImportLaps', laps })
  }

  // Start editing a lap label
  const startEditingSection = (idx: number) => {
    setEditingLap(idx)
    setEditingDuration(null)
    setEditText(model.laps[idx].section)
    setTimeout(() => sectionInputRef.current?.focus(), 0)
  }

  // Start editing a lap duration
  const startEditingDuration = (idx: number) => {
    setEditingDuration(idx)
    setEditingLap(null)
    setEditDurationText(formatTime(model.laps[idx].duration))
    setTimeout(() => durationInputRef.current?.select(), 0)
  }

  // Keyboard shortcuts
  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      // Ignore if editing
      if (editingLap !== null || editingDuration !== null || editingTagsIdx !== null) return

      if (e.key === ' ' && !e.metaKey && !e.ctrlKey) {
        e.preventDefault()
        if (running) {
          createLap()
        } else {
          toggleTimer()
        }
      } else if (e.key === 'z' && (e.metaKey || e.ctrlKey) && !e.shiftKey) {
        e.preventDefault()
        undo()
      } else if ((e.key === 'z' && (e.metaKey || e.ctrlKey) && e.shiftKey) ||
                 (e.key === 'y' && (e.metaKey || e.ctrlKey))) {
        e.preventDefault()
        redo()
      }
    }

    window.addEventListener('keydown', handleKeyDown)
    return () => window.removeEventListener('keydown', handleKeyDown)
  }, [running, editingLap, editingDuration, editingTagsIdx, undo, redo])

  const selectedTotal = getSelectedTotal(model.laps)
  const selectedCount = getSelectedCount(model.laps)
  const tagTotals = getTagTotals(model.laps)

  // Copy markdown to clipboard
  const copyMarkdown = async () => {
    const md = generateMarkdown(model.laps)
    await navigator.clipboard.writeText(md)
  }

  return (
    <div className="app">
      <button onClick={importMarkdown} className="import-btn" title="Import from clipboard">
        Paste Import
      </button>

      <div className="timer-display">
        <div className="time">{formatTime(displayTime)}</div>
      </div>

      <div className="controls">
        <button onClick={toggleTimer} className="control-btn">
          {running ? 'Pause' : (startTime ? 'Resume' : 'Start')}
        </button>
        <button
          onClick={createLap}
          className={`control-btn lap-btn ${!running ? 'hidden' : ''}`}
          disabled={!running}
        >
          Lap
        </button>
        <button
          onClick={resetTimer}
          className={`control-btn reset-btn ${model.laps.length === 0 ? 'hidden' : ''}`}
          disabled={model.laps.length === 0}
        >
          Reset
        </button>
      </div>

      <div className="undo-redo">
        <button onClick={undo} disabled={!canUndo} className="undo-btn">
          Undo
        </button>
        <button onClick={redo} disabled={!canRedo} className="redo-btn">
          Redo
        </button>
        {model.laps.some(lap => lap.section !== '') && model.template.length === 0 && (
          <button onClick={startPractice} className="practice-btn">
            Practice
          </button>
        )}
      </div>

      {model.template.length > 0 && (
        <div className="template-queue">
          <span className="queue-label">Next:</span>
          <span className="queue-item">
            {model.template[0].section} (expected {formatTime(model.template[0].expectedDuration)})
          </span>
          {model.template.length > 1 && (
            <span className="queue-remaining">+{model.template.length - 1} more</span>
          )}
        </div>
      )}

      {model.laps.length > 0 && (
        <div className="laps">
          <h3>Takes</h3>
          <ul className="lap-list">
            {model.laps.map((lap, idx) => {
              const isEditingSection = editingLap === idx
              const isEditingDur = editingDuration === idx

              return (
                <li key={idx} className={`lap-item ${lap.selected ? 'selected' : ''}`}>
                  <button
                    className={`select-btn ${lap.selected ? 'selected' : ''}`}
                    onClick={() => toggleSelect(idx)}
                    title={lap.selected ? 'Remove from total' : 'Add to total'}
                  >
                    {lap.selected ? '✓' : '○'}
                  </button>

                  {isEditingDur ? (
                    <input
                      ref={durationInputRef}
                      type="text"
                      value={editDurationText}
                      onChange={e => setEditDurationText(e.target.value)}
                      onBlur={() => adjustDuration(idx, editDurationText)}
                      onKeyDown={e => {
                        if (e.key === 'Enter') adjustDuration(idx, editDurationText)
                        if (e.key === 'Escape') setEditingDuration(null)
                      }}
                      className="duration-input"
                      placeholder="0:00"
                    />
                  ) : (
                    <span
                      className="lap-duration"
                      onClick={() => startEditingDuration(idx)}
                      title="Click to edit duration"
                    >
                      {formatTime(lap.duration)}
                    </span>
                  )}

                  {isEditingSection ? (
                    <input
                      ref={sectionInputRef}
                      type="text"
                      value={editText}
                      onChange={e => setEditText(e.target.value)}
                      onBlur={() => labelLap(idx, editText)}
                      onKeyDown={e => {
                        if (e.key === 'Enter') labelLap(idx, editText)
                        if (e.key === 'Escape') setEditingLap(null)
                      }}
                      className="section-input"
                      placeholder=""
                    />
                  ) : (
                    <span
                      className="lap-section"
                      onClick={() => startEditingSection(idx)}
                    >
                      {lap.section || '...'}
                    </span>
                  )}

                  <div className="tag-container">
                    {lap.tags.map(tag => (
                      <span key={tag} className="tag-chip">
                        {tag}
                        <button
                          className="tag-remove"
                          onClick={() => removeTag(idx, tag)}
                          title="Remove tag"
                        >
                          ×
                        </button>
                      </span>
                    ))}
                    {editingTagsIdx === idx ? (
                      <input
                        ref={tagInputRef}
                        type="text"
                        value={newTagText}
                        onChange={e => setNewTagText(e.target.value)}
                        onBlur={() => addTag(idx, newTagText)}
                        onKeyDown={e => {
                          if (e.key === 'Enter') addTag(idx, newTagText)
                          if (e.key === 'Escape') setEditingTagsIdx(null)
                        }}
                        className="tag-input"
                        placeholder="Tag..."
                      />
                    ) : (
                      <button
                        className="add-tag-btn"
                        onClick={() => startEditingTags(idx)}
                        title="Add tag"
                      >
                        +
                      </button>
                    )}
                  </div>

                  {lap.expectedDuration >= 0 && (
                    <span className="expected-duration">(was {formatTime(lap.expectedDuration)})</span>
                  )}

                  <button
                    className="move-btn"
                    onClick={() => moveUp(idx)}
                    disabled={idx === 0}
                    title="Move up"
                  >
                    ↑
                  </button>
                  <button
                    className="move-btn"
                    onClick={() => moveDown(idx)}
                    disabled={idx === model.laps.length - 1}
                    title="Move down"
                  >
                    ↓
                  </button>

                  <button
                    className="delete-btn"
                    onClick={() => deleteLap(idx)}
                    title="Delete this take"
                  >
                    ×
                  </button>
                </li>
              )
            })}
          </ul>
        </div>
      )}

      {selectedCount > 0 && (
        <div className="selected-total">
          <span className="total-label">Total:</span>
          <span className="total-time">{formatTime(selectedTotal)}</span>
          <span className="total-count">({selectedCount} takes)</span>
          <button onClick={copyMarkdown} className="copy-btn" title="Copy as Markdown">
            Copy
          </button>
        </div>
      )}

      {tagTotals.length > 0 && (
        <div className="tag-totals">
          <h3>By Tag</h3>
          <div className="tag-totals-list">
            {tagTotals.map(({ tag, total, count }) => (
              <div key={tag} className="tag-total-item">
                <span className="tag-total-name">{tag}</span>
                <span className="tag-total-time">{formatTime(total)}</span>
                <span className="tag-total-count">({count})</span>
              </div>
            ))}
          </div>
        </div>
      )}

    </div>
  )
}

export default App
