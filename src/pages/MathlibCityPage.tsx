import { useEffect, useMemo, useRef, useState } from 'react'
import * as THREE from 'three'
import { PointerLockControls } from 'three/examples/jsm/controls/PointerLockControls.js'
import RAPIER from '@dimforge/rapier3d-compat'
import { SiteHeader } from '../components/SiteHeader'
import { useThemeMode } from '../hooks/useThemeMode'
import '../App.css'

type TreemapNode = {
  name: string
  path?: string
  series: Record<string, number>
  kind?: string
  children?: TreemapNode[]
  isLeaf?: boolean
}

type TreemapData = {
  root: TreemapNode
  seriesKeys: string[]
}

type LayoutNode = {
  name: string
  path?: string
  series: Record<string, number>
  kind?: string
  isLeaf?: boolean
  x0: number
  y0: number
  x1: number
  y1: number
  fill: string
  parentName?: string
}

type LayoutPayload = {
  leafNodes: LayoutNode[]
}

export const MathlibCityPage = () => {
  const containerRef = useRef<HTMLDivElement>(null)
  const { mode, setMode, theme } = useThemeMode()
  const [isFullscreen, setIsFullscreen] = useState(false)
  const [isLocked, setIsLocked] = useState(false)
  const [showOverlay, setShowOverlay] = useState(true)
  const [layout, setLayout] = useState<LayoutPayload | null>(null)
  const [sizeSeries, setSizeSeries] = useState<string>('loc')
  const [physicsReady, setPhysicsReady] = useState(false)
  const [hoveredInfo, setHoveredInfo] = useState<LayoutNode | null>(null)
  const [hudStats, setHudStats] = useState({ x: 0, y: 0, z: 0, speed: 0 })
  const [perfStats, setPerfStats] = useState({ fps: 0, calls: 0, tris: 0, chunks: 0, chunksVisible: 0 })
  const speedRef = useRef(18)
  const spawnRef = useRef({ x: 0, y: 2, z: 1430 })
  const layoutSize = useMemo(() => ({ width: 1000, height: 1000 }), [])
  const sceneRef = useRef<THREE.Scene | null>(null)
  const cameraRef = useRef<THREE.PerspectiveCamera | null>(null)
  const rendererRef = useRef<THREE.WebGLRenderer | null>(null)
  const instancedMeshesRef = useRef<THREE.InstancedMesh[]>([])
  const hoveredMeshRef = useRef<THREE.InstancedMesh | null>(null)
  const hoveredInstanceRef = useRef<number | null>(null)
  const controlsRef = useRef<PointerLockControls | null>(null)
  const rapierRef = useRef<typeof RAPIER | null>(null)
  const worldRef = useRef<RAPIER.World | null>(null)
  const playerRef = useRef<RAPIER.RigidBody | null>(null)
  const playerColliderRef = useRef<RAPIER.Collider | null>(null)
  const controllerRef = useRef<RAPIER.KinematicCharacterController | null>(null)
  const groundedRef = useRef<boolean>(false)
  const controllerReadyRef = useRef<boolean>(false)
  const cityBodyRef = useRef<RAPIER.RigidBody | null>(null)
  const raycasterRef = useRef<THREE.Raycaster | null>(null)
  const buildingInfoRef = useRef<LayoutNode[]>([])
  const buildingColorRef = useRef<THREE.Color[]>([])
  const highlightColorRef = useRef(new THREE.Color())
  const highlightTargetRef = useRef(new THREE.Color('#ffffff'))
  const outlineRef = useRef<THREE.InstancedMesh | null>(null)
  const outlinesRef = useRef<THREE.LineSegments[]>([])
  const outlineMatrixRef = useRef(new THREE.Matrix4())
  const outlinePositionRef = useRef(new THREE.Vector3())
  const outlineQuaternionRef = useRef(new THREE.Quaternion())
  const outlineScaleRef = useRef(new THREE.Vector3())
  const gridRef = useRef<THREE.GridHelper | null>(null)
  const sidewalkRef = useRef<THREE.InstancedMesh | null>(null)
  const perfFrameCountRef = useRef(0)
  const perfLastUpdateRef = useRef(0)
  const frustumRef = useRef(new THREE.Frustum())
  const projScreenMatrixRef = useRef(new THREE.Matrix4())
  const lastHudUpdateRef = useRef(0)
  const lockedRef = useRef(false)
  const gravityEnabledRef = useRef(false)
  const verticalVelocityRef = useRef(0)

  const palette = useMemo(() => ([
    '#ffd8be',
    '#cde7f0',
    '#d7f3d0',
    '#f7d6e0',
    '#e6defa',
    '#ffeaa7',
    '#c9f6f4',
    '#f6f0b2',
    '#f6c9d0',
    '#d0e6ff',
    '#e7f0c3',
    '#f4e1c1',
  ]), [])

  useEffect(() => {
    const handleFullscreenChange = () => {
      setIsFullscreen(Boolean(document.fullscreenElement))
      resize()
      window.setTimeout(resize, 0)
      window.setTimeout(resize, 150)
    }
    document.addEventListener('fullscreenchange', handleFullscreenChange)

    const container = containerRef.current
    if (!container) {
      return () => {
        document.removeEventListener('fullscreenchange', handleFullscreenChange)
      }
    }

    const scene = new THREE.Scene()
    scene.background = new THREE.Color('#cfe3f7')
    scene.fog = new THREE.Fog('#cfe3f7', 400, 2400)
    sceneRef.current = scene

    const camera = new THREE.PerspectiveCamera(80, 1, 0.1, 4000)
    camera.position.set(0, 8, 18)
    camera.lookAt(0, 0, 0)
    cameraRef.current = camera

    const controls = new PointerLockControls(camera, container)
    controlsRef.current = controls
    scene.add(controls.object)

    const handleLock = () => {
      lockedRef.current = true
      setIsLocked(true)
    }
    const handleUnlock = () => {
      lockedRef.current = false
      setIsLocked(false)
    }
    controls.addEventListener('lock', handleLock)
    controls.addEventListener('unlock', handleUnlock)

    const renderer = new THREE.WebGLRenderer({ antialias: true })
    renderer.setPixelRatio(window.devicePixelRatio)
    container.appendChild(renderer.domElement)
    rendererRef.current = renderer

    const ambient = new THREE.AmbientLight(0xffffff, 0.5)
    scene.add(ambient)
    const sun = new THREE.DirectionalLight(0xffffff, 1.1)
    sun.position.set(40, 80, 20)
    sun.castShadow = false
    scene.add(sun)
    const sky = new THREE.HemisphereLight(0xffffff, 0x8899aa, 0.6)
    scene.add(sky)

    const ground = new THREE.Mesh(
      new THREE.PlaneGeometry(8000, 8000),
      new THREE.MeshStandardMaterial({
        color: '#151b22',
        polygonOffset: true,
        polygonOffsetFactor: 1,
        polygonOffsetUnits: 1,
      }),
    )
    ground.rotation.x = -Math.PI / 2
    scene.add(ground)

    let frameId = 0
    const clock = new THREE.Clock()

    const resize = () => {
      const { clientWidth, clientHeight } = container
      renderer.setSize(clientWidth, clientHeight)
      camera.aspect = clientWidth / Math.max(1, clientHeight)
      camera.updateProjectionMatrix()
    }

    const keys = new Set<string>()
    const normalizeKey = (event: KeyboardEvent) => {
      if (event.code === 'Space') {
        return 'space'
      }
      if (event.code === 'ShiftLeft' || event.code === 'ShiftRight') {
        return 'shift'
      }
      return event.key.toLowerCase()
    }
    const handleKeyDown = (event: KeyboardEvent) => {
      if (lockedRef.current && (event.code === 'Space' || event.code === 'ShiftLeft' || event.code === 'ShiftRight')) {
        event.preventDefault()
      }
      const key = normalizeKey(event)
      if (key === 'o') {
        setShowOverlay((current) => !current)
        return
      }
      if (key === 'g') {
        gravityEnabledRef.current = !gravityEnabledRef.current
        verticalVelocityRef.current = 0
        return
      }
      if (key === 'r') {
        speedRef.current = speedRef.current * 2
        return
      }
      if (key === 'f') {
        speedRef.current = speedRef.current / 2
        return
      }
      keys.add(key)
    }
    const handleKeyUp = (event: KeyboardEvent) => {
      keys.delete(normalizeKey(event))
    }
    const handleBlur = () => {
      keys.clear()
    }
    window.addEventListener('keydown', handleKeyDown)
    window.addEventListener('keyup', handleKeyUp)
    window.addEventListener('blur', handleBlur)

    let elapsed = 0
    const animate = () => {
      const delta = clock.getDelta()
      elapsed += delta
      perfFrameCountRef.current += 1
      if (
        controlsRef.current &&
        worldRef.current &&
        playerRef.current &&
        playerColliderRef.current &&
        controllerRef.current
      ) {
        const controls = controlsRef.current
        const player = playerRef.current
        const playerCollider = playerColliderRef.current
        const moveSpeed = speedRef.current
        const forward = new THREE.Vector3()
        controls.getDirection(forward)
        forward.y = 0
        forward.normalize()
        const right = new THREE.Vector3().crossVectors(forward, new THREE.Vector3(0, 1, 0))
        const velocity = new THREE.Vector3()
        if (keys.has('w')) velocity.add(forward)
        if (keys.has('s')) velocity.sub(forward)
        if (keys.has('a')) velocity.sub(right)
        if (keys.has('d')) velocity.add(right)
        if (velocity.lengthSq() > 0) {
          velocity.normalize().multiplyScalar(moveSpeed)
        }
        const controller = controllerRef.current
        const desired = new THREE.Vector3(velocity.x, 0, velocity.z)
        if (gravityEnabledRef.current) {
          const gravity = -24
          if (groundedRef.current && verticalVelocityRef.current < 0) {
            verticalVelocityRef.current = 0
          }
          if (keys.has('space') && groundedRef.current) {
            verticalVelocityRef.current = 25
          }
          verticalVelocityRef.current += gravity * delta
          desired.y = verticalVelocityRef.current
        } else if (keys.has('space')) {
          desired.y = moveSpeed / 2
        } else if (keys.has('shift')) {
          desired.y = -moveSpeed / 2
        }
        const needsControllerUpdate =
          desired.lengthSq() > 0 || gravityEnabledRef.current || !controllerReadyRef.current
        if (needsControllerUpdate) {
          controller.computeColliderMovement(
            playerCollider,
            { x: desired.x * delta, y: desired.y * delta, z: desired.z * delta },
          )
          const movement = controller.computedMovement()
          groundedRef.current = controller.computedGrounded()
          const translation = player.translation()
          player.setTranslation({
            x: translation.x + movement.x,
            y: translation.y + movement.y,
            z: translation.z + movement.z,
          }, true)
          controllerReadyRef.current = true
        }
        worldRef.current.step()
        const pos = player.translation()
        controls.object.position.set(pos.x, pos.y + 1.6, pos.z)
      }

      const meshes = instancedMeshesRef.current
      if (meshes.length > 0) {
        if (!raycasterRef.current) {
          raycasterRef.current = new THREE.Raycaster()
        }
        raycasterRef.current.setFromCamera(new THREE.Vector2(0, 0), camera)
        const hits = raycasterRef.current.intersectObjects(meshes, false)
        const hit = hits[0]
        const hitMesh = (hit?.object as THREE.InstancedMesh | undefined) ?? null
        const hitInstance = hit?.instanceId ?? null
        if (hitInstance !== hoveredInstanceRef.current || hitMesh !== hoveredMeshRef.current) {
          const previousMesh = hoveredMeshRef.current
          const previousInstance = hoveredInstanceRef.current
          hoveredMeshRef.current = hitMesh
          hoveredInstanceRef.current = hitInstance
          if (previousMesh && previousInstance !== null && previousMesh.instanceColor) {
            const previousGlobal = (previousMesh.userData.globalIndices as number[] | undefined)?.[previousInstance]
            if (previousGlobal !== undefined) {
              const previousColor = buildingColorRef.current[previousGlobal]
              if (previousColor) {
                previousMesh.setColorAt(previousInstance, previousColor)
                previousMesh.instanceColor.needsUpdate = true
              }
            }
          }
          if (hitMesh && hitInstance !== null && hitMesh.instanceColor) {
            const hitGlobal = (hitMesh.userData.globalIndices as number[] | undefined)?.[hitInstance]
            if (hitGlobal !== undefined) {
              setHoveredInfo(buildingInfoRef.current[hitGlobal] ?? null)
              const baseColor = buildingColorRef.current[hitGlobal]
              if (baseColor) {
                const highlight = highlightColorRef.current
                highlight.copy(baseColor).lerp(highlightTargetRef.current, 0.55)
                hitMesh.setColorAt(hitInstance, highlight)
                hitMesh.instanceColor.needsUpdate = true
              }
            }
          } else {
            setHoveredInfo(null)
          }
          if (outlineRef.current) {
            if (!hitMesh || hitInstance === null) {
              outlineRef.current.visible = false
            } else {
              const outlineMatrix = outlineMatrixRef.current
              const outlinePosition = outlinePositionRef.current
              const outlineQuaternion = outlineQuaternionRef.current
              const outlineScale = outlineScaleRef.current
              hitMesh.getMatrixAt(hitInstance, outlineMatrix)
              outlineMatrix.decompose(outlinePosition, outlineQuaternion, outlineScale)
              outlineMatrix.compose(outlinePosition, outlineQuaternion, outlineScale)
              outlineRef.current.setMatrixAt(0, outlineMatrix)
              outlineRef.current.instanceMatrix.needsUpdate = true
              outlineRef.current.visible = true
            }
          }
        }
      }

      if (controlsRef.current && playerRef.current) {
        if (elapsed - lastHudUpdateRef.current > 0.1) {
          const pos = playerRef.current.translation()
          setHudStats({
            x: pos.x,
            y: pos.y,
            z: pos.z,
            speed: speedRef.current,
          })
          lastHudUpdateRef.current = elapsed
        }
      }

      if (rendererRef.current && elapsed - perfLastUpdateRef.current > 0.5) {
        const timeWindow = elapsed - perfLastUpdateRef.current
        const fps = perfFrameCountRef.current / Math.max(timeWindow, 0.001)
        perfFrameCountRef.current = 0
        perfLastUpdateRef.current = elapsed

        const rendererInfo = rendererRef.current.info.render
        const meshes = instancedMeshesRef.current
        const frustum = frustumRef.current
        const projScreenMatrix = projScreenMatrixRef.current
        projScreenMatrix.multiplyMatrices(camera.projectionMatrix, camera.matrixWorldInverse)
        frustum.setFromProjectionMatrix(projScreenMatrix)
        let visibleChunks = 0
        meshes.forEach((mesh) => {
          mesh.updateMatrixWorld(false)
          if (frustum.intersectsObject(mesh)) {
            visibleChunks += 1
          }
        })

        setPerfStats({
          fps,
          calls: rendererInfo.calls,
          tris: rendererInfo.triangles,
          chunks: meshes.length,
          chunksVisible: visibleChunks,
        })
      }
      renderer.render(scene, camera)
      frameId = window.requestAnimationFrame(animate)
    }

    resize()
    window.addEventListener('resize', resize)
    animate()

    return () => {
      document.removeEventListener('fullscreenchange', handleFullscreenChange)
      window.removeEventListener('resize', resize)
      window.removeEventListener('keydown', handleKeyDown)
      window.removeEventListener('keyup', handleKeyUp)
      window.removeEventListener('blur', handleBlur)
      controls.removeEventListener('lock', handleLock)
      controls.removeEventListener('unlock', handleUnlock)
      window.cancelAnimationFrame(frameId)
      renderer.dispose()
      container.removeChild(renderer.domElement)
      ground.geometry.dispose()
      if (Array.isArray(ground.material)) {
        ground.material.forEach((mat: THREE.Material) => mat.dispose())
      } else {
        ground.material.dispose()
      }
    }
  }, [])

  useEffect(() => {
    let cancelled = false
    const setupPhysics = async () => {
      await RAPIER.init()
      if (cancelled) {
        return
      }
      rapierRef.current = RAPIER
      const world = new RAPIER.World({ x: 0, y: -9.81, z: 0 })
      worldRef.current = world

      const ground = world.createRigidBody(RAPIER.RigidBodyDesc.fixed())
      world.createCollider(
        RAPIER.ColliderDesc.cuboid(4000, 0.1, 4000).setTranslation(0, 0, 0),
        ground,
      )

      const spawn = spawnRef.current
      const bodyDesc = RAPIER.RigidBodyDesc.kinematicPositionBased()
        .setTranslation(spawn.x, spawn.y, spawn.z)
        .lockRotations()
      const body = world.createRigidBody(bodyDesc)
      const playerCollider = world.createCollider(RAPIER.ColliderDesc.capsule(0.65, 0.25), body)
      playerRef.current = body
      playerColliderRef.current = playerCollider
      const controller = world.createCharacterController(0.05)
      controller.enableSnapToGround(0.2)
      controller.setApplyImpulsesToDynamicBodies(true)
      controllerRef.current = controller
      setPhysicsReady(true)
    }
    void setupPhysics()
    return () => {
      cancelled = true
    }
  }, [])

  useEffect(() => {
    let active = true
    let worker: Worker | null = null
    const loadData = async () => {
      try {
        const url = new URL('./mathlib_treemap.json', window.location.href)
        const response = await fetch(url.toString())
        if (!response.ok) {
          throw new Error(`Failed to load treemap data: ${response.status}`)
        }
        const parsed = (await response.json()) as TreemapData
        if (!active) {
          return
        }
        const preferred = parsed.seriesKeys.includes('loc')
          ? 'loc'
          : parsed.seriesKeys[0] ?? 'loc'
        setSizeSeries(preferred)

        worker = new Worker(
          new URL('../workers/treemapWorker.ts', import.meta.url),
          { type: 'module' },
        )
        const requestId = 1
        worker.onmessage = (event: MessageEvent<{ type: string; requestId: number; payload: LayoutPayload }>) => {
          if (event.data.type !== 'layout' || event.data.requestId !== requestId) {
            return
          }
          if (!active) {
            return
          }
          setLayout(event.data.payload)
          worker?.terminate()
        }
        worker.postMessage({
          type: 'layout',
          requestId,
          payload: {
            data: parsed.root,
            sizeSeries: preferred,
            colorSeries: preferred,
            colorMode: 'global',
            theme,
            width: layoutSize.width,
            height: layoutSize.height,
            colors: palette,
          },
        })
      } catch (error) {
        console.warn('Failed to load city data', error)
      }
    }
    void loadData()
    return () => {
      active = false
      worker?.terminate()
    }
  }, [layoutSize.height, layoutSize.width, palette, theme])

  useEffect(() => {
    const scene = sceneRef.current
    const camera = cameraRef.current
    if (!scene || !camera || !layout) {
      return
    }

    if (instancedMeshesRef.current.length > 0) {
      instancedMeshesRef.current.forEach((mesh) => {
        scene.remove(mesh)
        mesh.geometry.dispose()
        if (Array.isArray(mesh.material)) {
          mesh.material.forEach((mat: THREE.Material) => mat.dispose())
        } else {
          mesh.material.dispose()
        }
      })
      instancedMeshesRef.current = []
    }
    if (gridRef.current) {
      scene.remove(gridRef.current)
      if (Array.isArray(gridRef.current.material)) {
        gridRef.current.material.forEach((mat) => mat.dispose())
      } else {
        gridRef.current.material.dispose()
      }
      gridRef.current = null
    }
    if (sidewalkRef.current) {
      scene.remove(sidewalkRef.current)
      sidewalkRef.current.geometry.dispose()
      if (Array.isArray(sidewalkRef.current.material)) {
        sidewalkRef.current.material.forEach((mat: THREE.Material) => mat.dispose())
      } else {
        sidewalkRef.current.material.dispose()
      }
      sidewalkRef.current = null
    }
    if (outlineRef.current) {
      scene.remove(outlineRef.current)
      outlineRef.current.geometry.dispose()
      if (Array.isArray(outlineRef.current.material)) {
        outlineRef.current.material.forEach((mat: THREE.Material) => mat.dispose())
      } else {
        outlineRef.current.material.dispose()
      }
      outlineRef.current = null
    }
    if (outlinesRef.current.length > 0) {
      outlinesRef.current.forEach((mesh) => {
        scene.remove(mesh)
        mesh.geometry.dispose()
        if (Array.isArray(mesh.material)) {
          mesh.material.forEach((mat: THREE.Material) => mat.dispose())
        } else {
          mesh.material.dispose()
        }
      })
      outlinesRef.current = []
    }

    const leaves = layout.leafNodes
    buildingInfoRef.current = leaves
    buildingColorRef.current = []
    hoveredMeshRef.current = null
    hoveredInstanceRef.current = null
    setHoveredInfo(null)
    const dummy = new THREE.Object3D()
    const worldWidth = 2000
    const worldDepth = 2000
    const blockSizeX = 60
    const blockSizeZ = 243
    const streetWidth = 18.3
    const sidewalkWidth = Math.min(6, Math.max(2, (streetWidth - 6) / 2))
    const alleyWidth = 0
    const minFootprint = 8
    const blockSpanX = blockSizeX + streetWidth
    const blockSpanZ = blockSizeZ + streetWidth
    const blocksX = Math.max(1, Math.floor(worldWidth / blockSpanX))
    const blocksZ = Math.max(1, Math.floor(worldDepth / blockSpanZ))
    const citySizeX = blocksX * blockSpanX
    const citySizeZ = blocksZ * blockSpanZ
    const cityOriginX = -citySizeX / 2 + blockSpanX / 2
    const cityOriginZ = -citySizeZ / 2 + blockSpanZ / 2
    const totalValue = leaves.reduce((sum, leaf) => sum + (leaf.series?.[sizeSeries] ?? 0), 0)
    const heightMax = Math.max(1, ...leaves.map((leaf) => leaf.series?.[sizeSeries] ?? 0))
    const totalBuildableArea = blocksX * blocksZ * blockSizeX * blockSizeZ * 0.7
    const areaScale = totalValue > 0 ? totalBuildableArea / totalValue : 0
    const chunkSize = 250
    const chunkMap = new Map<string, number[]>()
    const categoryColors = new Map<string, string>()
    let paletteIndex = 0

    const hashToUnit = (seed: string) => {
      let hash = 0
      for (let i = 0; i < seed.length; i += 1) {
        hash = (hash * 31 + seed.charCodeAt(i)) | 0
      }
      const normalized = Math.abs(hash % 10000) / 10000
      return normalized
    }

    const sortedLeaves = leaves
      .map((leaf, index) => ({ leaf, index }))
      .sort((a, b) => (b.leaf.series?.[sizeSeries] ?? 0) - (a.leaf.series?.[sizeSeries] ?? 0))

    const instances: Array<{
      index: number
      x: number
      z: number
      width: number
      depth: number
      height: number
      color: THREE.Color
      block?: number
    }> = []

    const neighborhoodMap = new Map<string, Map<string, Array<{ leaf: LayoutNode; index: number }>>>()
    sortedLeaves.forEach((item) => {
      const parts = (item.leaf.path ?? '').split('/')
      const neighborhood = parts.length > 1 ? parts[1] : 'Mathlib'
      const subgroup = parts.length > 2 ? parts[2] : 'Core'
      const subgroupMap = neighborhoodMap.get(neighborhood) ?? new Map()
      const list = subgroupMap.get(subgroup) ?? []
      list.push(item)
      subgroupMap.set(subgroup, list)
      neighborhoodMap.set(neighborhood, subgroupMap)
    })

    const neighborhoods = Array.from(neighborhoodMap.entries()).map(([name, subgroupMap]) => {
      const items = Array.from(subgroupMap.entries()).map(([subgroup, subItems]) => {
        const total = subItems.reduce((sum, item) => sum + (item.leaf.series?.[sizeSeries] ?? 0), 0)
        return { subgroup, items: subItems, total }
      }).sort((a, b) => b.total - a.total)
      const total = items.reduce((sum, item) => sum + item.total, 0)
      return { name, items, total }
    }).sort((a, b) => b.total - a.total)

    const blocksTotal = blocksX * blocksZ
    const blockCoords = Array.from({ length: blocksTotal }, (_, idx) => ({
      index: idx,
      gx: idx % blocksX,
      gz: Math.floor(idx / blocksX),
    }))
    const availableBlocks = new Set(blockCoords.map((block) => block.index))
    const neighborhoodBlocks = new Map<string, number[]>()

    neighborhoods.forEach((neighborhood) => {
      if (availableBlocks.size === 0) {
        return
      }
      const blocksNeeded = Math.max(1, Math.ceil((neighborhood.total * areaScale) / (blockSizeX * blockSizeZ * 0.7)))
      const availableList = Array.from(availableBlocks)
      const seedIndex = availableList[Math.floor(hashToUnit(neighborhood.name) * availableList.length)]
      const seed = blockCoords[seedIndex]
      const sortedBlocks = availableList.sort((a, b) => {
        const aCoord = blockCoords[a]
        const bCoord = blockCoords[b]
        const da = (aCoord.gx - seed.gx) ** 2 + (aCoord.gz - seed.gz) ** 2
        const db = (bCoord.gx - seed.gx) ** 2 + (bCoord.gz - seed.gz) ** 2
        return da - db
      })
      const assignedBlocks = sortedBlocks.slice(0, blocksNeeded)
      assignedBlocks.forEach((block) => availableBlocks.delete(block))
      neighborhoodBlocks.set(neighborhood.name, assignedBlocks)
    })

    const blockProfiles = Array.from({ length: blocksTotal }, (_, idx) => {
      const densitySeed = hashToUnit(`density-${idx}`)
      return {
        alley: alleyWidth * (0.6 + densitySeed * 1.1),
        padding: 0,
      }
    })

    const occupiedBlocks = new Set<number>()

    neighborhoods.forEach((neighborhood) => {
      const assignedBlocks = neighborhoodBlocks.get(neighborhood.name) ?? []
      if (assignedBlocks.length === 0) {
        return
      }
      let blockCursorIndex = 0
      let columnDepths: [number, number] = [0, 0]
      let columnWidth = 0
      let columnGap = 0
      let activeInnerX = 0
      let activeInnerZ = 0
      let activePaddingX = 0
      let activePaddingZ = 0
      let blockIndex = assignedBlocks[blockCursorIndex]

      const initBlock = () => {
        if (blockCursorIndex >= assignedBlocks.length) {
          return false
        }
        blockIndex = assignedBlocks[blockCursorIndex]
        const profile = blockProfiles[blockIndex]
        columnGap = profile.alley
        activePaddingX = Math.min(profile.padding, (blockSizeX - minFootprint) / 2)
        activePaddingZ = Math.min(profile.padding, (blockSizeZ - minFootprint) / 2)
        activeInnerX = Math.max(minFootprint, blockSizeX - activePaddingX * 2)
        activeInnerZ = Math.max(minFootprint, blockSizeZ - activePaddingZ * 2)
        columnWidth = Math.max(minFootprint, (activeInnerX - columnGap) / 2)
        columnDepths = [0, 0]
        return true
      }

      if (!initBlock()) {
        return
      }

      const orderedItems = neighborhood.items.flatMap((group) => {
        return group.items
          .slice()
          .sort((a, b) => hashToUnit(a.leaf.path ?? '') - hashToUnit(b.leaf.path ?? ''))
      })
      const shuffleInPlace = (items: Array<{ leaf: LayoutNode; index: number }>, seed: string) => {
        let state = Math.floor(hashToUnit(seed) * 1_000_000_000) | 0
        const next = () => {
          state ^= state << 13
          state ^= state >> 17
          state ^= state << 5
          return (state >>> 0) / 0xffffffff
        }
        for (let i = items.length - 1; i > 0; i -= 1) {
          const j = Math.floor(next() * (i + 1))
          const temp = items[i]
          items[i] = items[j]
          items[j] = temp
        }
      }
      shuffleInPlace(orderedItems, neighborhood.name)

      type Placement = {
        index: number
        width: number
        depth: number
        x: number
        z: number
        column: 0 | 1
        block: number
        area: number
        localZ: number
        paddingX: number
        paddingZ: number
        columnWidth: number
        columnGap: number
      }

      const placements: Placement[] = []
      let activeBlockPlacements: Placement[] = []

      const finalizeBlock = (block: number, innerZ: number, gap: number, columnWidthBase: number) => {
        const blockPlacements = activeBlockPlacements.filter((p) => p.block === block)
        if (blockPlacements.length === 0) {
          return
        }
        const columns: Array<Placement[]> = [[], []]
        blockPlacements.forEach((placement) => {
          columns[placement.column].push(placement)
        })
        columns.forEach((columnPlacements) => {
          if (columnPlacements.length === 0) {
            return
          }
          columnPlacements.sort((a, b) => a.localZ - b.localZ)
          const totalDepth = columnPlacements.reduce((sum, placement) => sum + placement.depth, 0)
          const totalGaps = gap * Math.max(0, columnPlacements.length - 1)
          const used = totalDepth + totalGaps
          if (used <= 0) {
            return
          }
          const scale = Math.min(1.15, Math.max(0.85, innerZ / used))
          let cursor = 0
          columnPlacements.forEach((placement, idx) => {
            const scaledDepth = placement.depth * scale
            const targetWidth = placement.area / scaledDepth
            const clampedWidth = Math.min(columnWidthBase, Math.max(minFootprint, targetWidth))
            const adjustedDepth = placement.area / clampedWidth
            placement.width = clampedWidth
            placement.depth = adjustedDepth
            placement.localZ = cursor + adjustedDepth / 2
            cursor += adjustedDepth + (idx === columnPlacements.length - 1 ? 0 : gap * scale)
          })
        })
      }

      orderedItems.forEach(({ leaf, index }) => {
        if (blockCursorIndex >= assignedBlocks.length) {
          return
        }
        const value = leaf.series?.[sizeSeries] ?? 0
        const area = Math.max(value * areaScale, minFootprint * minFootprint)
        let width = columnWidth
        let depth = area / Math.max(width, minFootprint)
        if (depth < minFootprint) {
          depth = minFootprint
        }
        let columnIndex: 0 | 1 = columnDepths[0] <= columnDepths[1] ? 0 : 1
        if (columnDepths[columnIndex] + depth > activeInnerZ) {
          finalizeBlock(blockIndex, activeInnerZ, columnGap, columnWidth)
          blockCursorIndex += 1
          if (!initBlock()) {
            return
          }
          columnIndex = columnDepths[0] <= columnDepths[1] ? 0 : 1
          if (columnDepths[columnIndex] + depth > activeInnerZ) {
            return
          }
          width = columnWidth
        }
        const blockX = blockIndex % blocksX
        const blockZ = Math.floor(blockIndex / blocksX)
        const originX = cityOriginX + blockX * blockSpanX
        const originZ = cityOriginZ + blockZ * blockSpanZ
        const x =
          columnIndex === 0
            ? originX + (activePaddingX + width / 2 - blockSizeX / 2)
            : originX + (blockSizeX / 2 - activePaddingX - width / 2)
        const z = originZ + (activePaddingZ + columnDepths[columnIndex] + depth / 2 - blockSizeZ / 2)
        const localZ = columnDepths[columnIndex] + depth / 2
        columnDepths[columnIndex] += depth + columnGap
        const path = leaf.path ?? ''
        const parts = path.split('/')
        const category = parts.length > 1 ? parts[1] : 'Mathlib'
        if (!categoryColors.has(category)) {
          categoryColors.set(category, palette[paletteIndex % palette.length])
          paletteIndex += 1
        }
        const colorHex = categoryColors.get(category) ?? palette[0]
        const baseColor = new THREE.Color(colorHex)
        buildingColorRef.current[index] = baseColor.clone()
        const height = 2 + value / heightMax * 140
        const placement: Placement = {
          index,
          x,
          z,
          width,
          depth,
          column: columnIndex,
          block: blockIndex,
          area,
          localZ,
          paddingX: activePaddingX,
          paddingZ: activePaddingZ,
          columnWidth,
          columnGap,
        }
        placements.push(placement)
        activeBlockPlacements.push(placement)
        occupiedBlocks.add(blockIndex)
        instances[index] = {
          index,
          x,
          z,
          width,
          depth,
          height,
          color: baseColor,
          block: blockIndex,
        }
      })
      finalizeBlock(blockIndex, activeInnerZ, columnGap, columnWidth)
      placements.forEach((placement) => {
        const blockX = placement.block % blocksX
        const blockZ = Math.floor(placement.block / blocksX)
        const originX = cityOriginX + blockX * blockSpanX
        const originZ = cityOriginZ + blockZ * blockSpanZ
        placement.x =
          placement.column === 0
            ? originX + (placement.paddingX + placement.width / 2 - blockSizeX / 2)
            : originX + (blockSizeX / 2 - placement.paddingX - placement.width / 2)
        placement.z = originZ + (placement.paddingZ + placement.localZ - blockSizeZ / 2)
        instances[placement.index] = {
          index: placement.index,
          x: placement.x,
          z: placement.z,
          width: placement.width,
          depth: placement.depth,
          height: instances[placement.index]?.height ?? 2,
          color: instances[placement.index]?.color ?? new THREE.Color('#ffffff'),
          block: placement.block,
        }
      })
      activeBlockPlacements = []
    })

    const compactedBlocks = Array.from(occupiedBlocks)
    const compactGridSize = Math.ceil(Math.sqrt(compactedBlocks.length))
    const compactedMap = new Map<number, { gx: number; gz: number }>()
    const availableCells = new Set<number>()
    for (let gz = 0; gz < compactGridSize; gz += 1) {
      for (let gx = 0; gx < compactGridSize; gx += 1) {
        availableCells.add(gz * compactGridSize + gx)
      }
    }
    const pickSeedCell = () => {
      let bestCell: number | null = null
      let bestScore = Infinity
      availableCells.forEach((cell) => {
        const gx = cell % compactGridSize
        const gz = Math.floor(cell / compactGridSize)
        const dx = gx - (compactGridSize - 1) / 2
        const dz = gz - (compactGridSize - 1) / 2
        const score = dx * dx + dz * dz
        if (score < bestScore) {
          bestScore = score
          bestCell = cell
        }
      })
      return bestCell
    }
    const expandCluster = (seedCell: number, count: number) => {
      const queue = [seedCell]
      const cluster: number[] = []
      const visited = new Set<number>()
      while (queue.length > 0 && cluster.length < count) {
        const cell = queue.shift()!
        if (!availableCells.has(cell) || visited.has(cell)) {
          continue
        }
        visited.add(cell)
        availableCells.delete(cell)
        cluster.push(cell)
        const gx = cell % compactGridSize
        const gz = Math.floor(cell / compactGridSize)
        const neighbors = [
          [gx + 1, gz],
          [gx - 1, gz],
          [gx, gz + 1],
          [gx, gz - 1],
        ]
        neighbors.forEach(([nx, nz]) => {
          if (nx < 0 || nz < 0 || nx >= compactGridSize || nz >= compactGridSize) {
            return
          }
          const ncell = nz * compactGridSize + nx
          if (!visited.has(ncell) && availableCells.has(ncell)) {
            queue.push(ncell)
          }
        })
      }
      return cluster
    }

    neighborhoods.forEach((neighborhood) => {
      const blocks = (neighborhoodBlocks.get(neighborhood.name) ?? []).filter((block) => occupiedBlocks.has(block))
      if (blocks.length === 0 || availableCells.size === 0) {
        return
      }
      const seedCell = pickSeedCell()
      if (seedCell === null) {
        return
      }
      const clusterCells = expandCluster(seedCell, blocks.length)
      blocks.forEach((block, idx) => {
        const cell = clusterCells[idx]
        if (cell === undefined) {
          return
        }
        const gx = cell % compactGridSize
        const gz = Math.floor(cell / compactGridSize)
        compactedMap.set(block, { gx, gz })
      })
    })
    compactedBlocks.forEach((block) => {
      if (compactedMap.has(block) || availableCells.size === 0) {
        return
      }
      const seedCell = pickSeedCell()
      if (seedCell === null) {
        return
      }
      const gx = seedCell % compactGridSize
      const gz = Math.floor(seedCell / compactGridSize)
      availableCells.delete(seedCell)
      compactedMap.set(block, { gx, gz })
    })

    const compactedOriginX = -compactGridSize * blockSpanX / 2 + blockSpanX / 2
    const compactedOriginZ = -compactGridSize * blockSpanZ / 2 + blockSpanZ / 2

    instances.forEach((item) => {
      if (!item) {
        return
      }
      const blockIndex = item.block ?? 0
      const target = compactedMap.get(blockIndex)
      if (!target) {
        return
      }
      const oldBlockX = blockIndex % blocksX
      const oldBlockZ = Math.floor(blockIndex / blocksX)
      const oldOriginX = cityOriginX + oldBlockX * blockSpanX
      const oldOriginZ = cityOriginZ + oldBlockZ * blockSpanZ
      const newOriginX = compactedOriginX + target.gx * blockSpanX
      const newOriginZ = compactedOriginZ + target.gz * blockSpanZ
      const localX = item.x - oldOriginX
      const localZ = item.z - oldOriginZ
      item.x = newOriginX + localX
      item.z = newOriginZ + localZ
    })

    const cityRotation = -Math.PI / 4
    instancedMeshesRef.current = []
    const gridDivisions = Math.max(compactGridSize, compactGridSize)
    const gridSize = Math.max(compactGridSize * blockSpanX, compactGridSize * blockSpanZ)
    const gridHelper = new THREE.GridHelper(gridSize, gridDivisions, '#2e3847', '#1c222c')
    gridHelper.position.y = 0.02
    gridHelper.rotation.y = cityRotation
    if (Array.isArray(gridHelper.material)) {
      gridHelper.material.forEach((mat) => {
        mat.transparent = true
        mat.opacity = 0.45
      })
    } else {
      gridHelper.material.transparent = true
      gridHelper.material.opacity = 0.45
    }
    scene.add(gridHelper)
    gridRef.current = gridHelper

    chunkMap.clear()
    instances.forEach((item, index) => {
      if (!item) {
        return
      }
      const cellX = Math.floor((item.x + gridSize / 2) / chunkSize)
      const cellZ = Math.floor((item.z + gridSize / 2) / chunkSize)
      const key = `${cellX},${cellZ}`
      const list = chunkMap.get(key) ?? []
      list.push(index)
      chunkMap.set(key, list)
    })

    const sidewalkGeometry = new THREE.BoxGeometry(1, 0.3, 1)
    const sidewalkMaterial = new THREE.MeshStandardMaterial({
      color: '#cfd5df',
      polygonOffset: true,
      polygonOffsetFactor: -1,
      polygonOffsetUnits: -2,
    })
    const sidewalkCount = compactedBlocks.length * 4
    const sidewalkMesh = new THREE.InstancedMesh(sidewalkGeometry, sidewalkMaterial, sidewalkCount)
    let sidewalkIndex = 0
    compactedBlocks.forEach((block) => {
      const target = compactedMap.get(block)
      if (!target) {
        return
      }
      const originX = compactedOriginX + target.gx * blockSpanX
      const originZ = compactedOriginZ + target.gz * blockSpanZ
        const halfX = blockSizeX / 2
        const halfZ = blockSizeZ / 2
        const offsetX = halfX + sidewalkWidth / 2
        const offsetZ = halfZ + sidewalkWidth / 2

        const edgeX = blockSizeX + sidewalkWidth * 2
        const edgeZ = blockSizeZ + sidewalkWidth * 2

        dummy.position.set(originX, 0.2, originZ - offsetZ)
        dummy.scale.set(edgeX, 1, sidewalkWidth)
        dummy.updateMatrix()
        sidewalkMesh.setMatrixAt(sidewalkIndex++, dummy.matrix)

        dummy.position.set(originX, 0.2, originZ + offsetZ)
        dummy.scale.set(edgeX, 1, sidewalkWidth)
        dummy.updateMatrix()
        sidewalkMesh.setMatrixAt(sidewalkIndex++, dummy.matrix)

        dummy.position.set(originX - offsetX, 0.2, originZ)
        dummy.scale.set(sidewalkWidth, 1, edgeZ)
        dummy.updateMatrix()
        sidewalkMesh.setMatrixAt(sidewalkIndex++, dummy.matrix)

      dummy.position.set(originX + offsetX, 0.2, originZ)
      dummy.scale.set(sidewalkWidth, 1, edgeZ)
      dummy.updateMatrix()
      sidewalkMesh.setMatrixAt(sidewalkIndex++, dummy.matrix)
    })
    sidewalkMesh.instanceMatrix.needsUpdate = true
    sidewalkMesh.rotation.y = cityRotation
    scene.add(sidewalkMesh)
    sidewalkRef.current = sidewalkMesh
    chunkMap.forEach((indices) => {
      const geometry = new THREE.BoxGeometry(1, 1, 1)
      const material = new THREE.MeshStandardMaterial({ color: '#ffffff' })
      const mesh = new THREE.InstancedMesh(geometry, material, indices.length)
      const globalIndices: number[] = []
      indices.forEach((globalIndex, instanceIndex) => {
        const item = instances[globalIndex]
        if (!item) {
          return
        }
        dummy.position.set(item.x, item.height / 2, item.z)
        dummy.scale.set(Math.max(item.width, 0.2), item.height, Math.max(item.depth, 0.2))
        dummy.updateMatrix()
        mesh.setMatrixAt(instanceIndex, dummy.matrix)
        mesh.setColorAt(instanceIndex, item.color)
        globalIndices[instanceIndex] = globalIndex
      })
      mesh.instanceMatrix.needsUpdate = true
      if (mesh.instanceColor) {
        mesh.instanceColor.needsUpdate = true
      }
      mesh.rotation.y = cityRotation
      mesh.computeBoundingBox()
      mesh.computeBoundingSphere()
      mesh.userData.globalIndices = globalIndices
      scene.add(mesh)
      instancedMeshesRef.current.push(mesh)

      const edgeGeometry = new THREE.EdgesGeometry(geometry)
      const edgePositions = edgeGeometry.getAttribute('position')
      const instanceCount = indices.length
      const mergedPositions = new Float32Array(edgePositions.count * 3 * instanceCount)
      const tempMatrix = new THREE.Matrix4()
      const tempVec = new THREE.Vector3()
      let writeIndex = 0
      for (let i = 0; i < instanceCount; i += 1) {
        mesh.getMatrixAt(i, tempMatrix)
        for (let v = 0; v < edgePositions.count; v += 1) {
          tempVec.set(
            edgePositions.getX(v),
            edgePositions.getY(v),
            edgePositions.getZ(v),
          )
          tempVec.applyMatrix4(tempMatrix)
          mergedPositions[writeIndex++] = tempVec.x
          mergedPositions[writeIndex++] = tempVec.y
          mergedPositions[writeIndex++] = tempVec.z
        }
      }
      const mergedGeometry = new THREE.BufferGeometry()
      mergedGeometry.setAttribute('position', new THREE.BufferAttribute(mergedPositions, 3))
      const outlineMaterial = new THREE.LineBasicMaterial({
        color: '#0f1116',
        transparent: true,
        opacity: 0.6,
      })
      const outlineLines = new THREE.LineSegments(mergedGeometry, outlineMaterial)
      outlineLines.rotation.y = cityRotation
      outlineLines.renderOrder = 2
      scene.add(outlineLines)
      outlinesRef.current.push(outlineLines)
    })

    const outlineGeometry = new THREE.BoxGeometry(1, 1, 1)
    const outlineMaterial = new THREE.MeshBasicMaterial({
      color: '#ffffff',
      transparent: true,
      opacity: 0.7,
      wireframe: true,
      depthWrite: false,
      depthTest: false,
      polygonOffset: true,
      polygonOffsetFactor: -1,
      polygonOffsetUnits: -1,
    })
    const outlineMesh = new THREE.InstancedMesh(outlineGeometry, outlineMaterial, 1)
    outlineMesh.rotation.y = cityRotation
    outlineMesh.frustumCulled = false
    outlineMesh.renderOrder = 3
    outlineMesh.visible = false
    scene.add(outlineMesh)
    outlineRef.current = outlineMesh

    if (worldRef.current && rapierRef.current) {
      const world = worldRef.current
      const rapier = rapierRef.current
      if (cityBodyRef.current) {
        world.removeRigidBody(cityBodyRef.current)
        cityBodyRef.current = null
      }
      const rotationQuat = new THREE.Quaternion().setFromAxisAngle(
        new THREE.Vector3(0, 1, 0),
        cityRotation,
      )
      const cityBody = world.createRigidBody(
        rapier.RigidBodyDesc.fixed().setRotation({
          x: rotationQuat.x,
          y: rotationQuat.y,
          z: rotationQuat.z,
          w: rotationQuat.w,
        }),
      )
      cityBodyRef.current = cityBody
      instances.forEach((item) => {
        if (!item) {
          return
        }
        const collider = rapier.ColliderDesc.cuboid(
          Math.max(item.width, 0.2) / 2,
          item.height / 2,
          Math.max(item.depth, 0.2) / 2,
        ).setTranslation(item.x, item.height / 2, item.z)
        world.createCollider(collider, cityBody)
      })
    }

    if (playerRef.current) {
      const spawn = spawnRef.current
      const eyeHeight = 1.6
      playerRef.current.setTranslation(spawn, true)
      controllerReadyRef.current = false
      if (controlsRef.current) {
        controlsRef.current.object.position.set(spawn.x, spawn.y + eyeHeight, spawn.z)
        controlsRef.current.object.lookAt(new THREE.Vector3(spawn.x, spawn.y + eyeHeight, spawn.z - 10))
      }
      camera.position.set(spawn.x, spawn.y + eyeHeight, spawn.z)
      camera.lookAt(spawn.x, spawn.y + eyeHeight, spawn.z - 10)
    }
  }, [layout, layoutSize.height, layoutSize.width, sizeSeries, physicsReady])

  const toggleFullscreen = async () => {
    const container = containerRef.current
    if (!container) {
      return
    }
    if (document.fullscreenElement) {
      await document.exitFullscreen()
    } else {
      await container.requestFullscreen()
    }
  }

  const handleCanvasClick = () => {
    controlsRef.current?.lock()
  }

  return (
    <div className={`page theme-${theme} city-page ${isFullscreen ? 'city-fullscreen' : ''}`}>
      <SiteHeader mode={mode} onModeChange={setMode} />
      <section className="panel">
        <div className="panel-header">

          <button className="ghost-button" onClick={toggleFullscreen}>
            {isFullscreen ? 'Exit Fullscreen' : 'Fullscreen'}
          </button>
        </div>
        <div className="city-canvas" ref={containerRef} onClick={handleCanvasClick}>
          {!isLocked && showOverlay ? (
            <div className="city-overlay">
              <div className="city-overlay-card">
                <h3>Click to enter</h3>
                <p>Mouse to look · WASD to move · Space/Shift to rise/descend · R/F speed · G gravity · O hide UI</p>
              </div>
            </div>
          ) : null}
          <div className="city-crosshair" />
          <div className="city-hud">
            <div className="city-hud-panel city-hud-left">
              <div className="city-hud-label">Focused building</div>
              {hoveredInfo ? (
                <>
                  <div className="city-hud-title">{hoveredInfo.name}.lean</div>
                  <div className="city-hud-path">{hoveredInfo.path ?? 'Unknown path'}</div>
                  <div className="city-hud-metrics">
                    {sizeSeries.toUpperCase()}: {Math.round(hoveredInfo.series?.[sizeSeries] ?? 0)}
                  </div>
                </>
              ) : (
                <div className="city-hud-muted">Look at a building to inspect details.</div>
              )}
            </div>
            <div className="city-hud-panel city-hud-right">
              <div className="city-hud-label">Position</div>
              <div className="city-hud-metrics">
                x {hudStats.x.toFixed(1)} · y {hudStats.y.toFixed(1)} · z {hudStats.z.toFixed(1)}
              </div>
              <div className="city-hud-label">Speed</div>
              <div className="city-hud-metrics">{hudStats.speed.toFixed(1)}</div>
              <div className="city-hud-label">Performance</div>
              <div className="city-hud-metrics">
                {perfStats.fps.toFixed(0)} fps · {perfStats.calls} calls · {Math.round(perfStats.tris / 1000)}k tris
              </div>
              <div className="city-hud-metrics">
                chunks {perfStats.chunksVisible}/{perfStats.chunks}
              </div>
            </div>
          </div>
        </div>
      </section>
      <button className="ghost-button city-fullscreen-toggle" onClick={toggleFullscreen}>
        {isFullscreen ? 'Exit Fullscreen' : 'Fullscreen'}
      </button>
    </div>
  )
}
